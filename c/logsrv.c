/* Framed TCP/TLS and the Lean I/O relay bridge. No protobuf or logging policy. */
#include "logsrv.h"
#include <arpa/inet.h>
#include <dlfcn.h>
#include <errno.h>
#include <fcntl.h>
#include <limits.h>
#include <netdb.h>
#include <poll.h>
#include <pthread.h>
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/socket.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <time.h>
#include <unistd.h>

#define LOGSRV_MAX_FRAME (2U * 1024U * 1024U)

/* OpenSSL 3's public, opaque ABI: no build-time OpenSSL dependency. */
typedef struct ssl_st SSL;
typedef struct ssl_ctx_st SSL_CTX;
typedef struct ssl_method_st SSL_METHOD;
typedef struct x509_st X509;
typedef struct x509_store_ctx_st X509_STORE_CTX;
struct tls_api {
  const SSL_METHOD *(*client_method)(void);
  SSL_CTX *(*ctx_new)(const SSL_METHOD *);
  void (*ctx_free)(SSL_CTX *);
  long (*ctx_ctrl)(SSL_CTX *, int, long, void *);
  void (*ctx_set_verify)(SSL_CTX *, int, int (*)(int, X509_STORE_CTX *));
  int (*ctx_load_ca)(SSL_CTX *, const char *, const char *);
  int (*ctx_default_ca)(SSL_CTX *);
  int (*ctx_use_cert)(SSL_CTX *, const char *);
  int (*ctx_use_key)(SSL_CTX *, const char *, int);
  int (*ctx_check_key)(const SSL_CTX *);
  SSL *(*ssl_new)(SSL_CTX *);
  void (*ssl_free)(SSL *);
  int (*ssl_set_fd)(SSL *, int);
  long (*ssl_ctrl)(SSL *, int, long, void *);
  X509 *(*ssl_peer_cert)(const SSL *);
  long (*ssl_verify_result)(const SSL *);
  int (*ssl_connect)(SSL *);
  int (*ssl_read)(SSL *, void *, int);
  int (*ssl_write)(SSL *, const void *, int);
  int (*ssl_error)(const SSL *, int);
  int (*cert_host)(X509 *, const char *, size_t, unsigned int, char **);
  int (*cert_ip)(X509 *, const unsigned char *, size_t, unsigned int);
  int (*cert_ext_by_nid)(const X509 *, int, int);
  void (*cert_free)(X509 *);
  void (*clear_error)(void);
  unsigned long (*get_error)(void);
  const char *(*reason_error)(unsigned long);
};
static struct {
  int fd, tls_errno;
  uint32_t timeout, relay;
  void *ssl_lib, *crypto_lib;
  struct tls_api api;
  SSL_CTX *ctx;
  SSL *ssl;
  unsigned char header[4];
  size_t header_used, body_used;
  lean_object *body;
} connection = {.fd = -1};

/* Independent lifetime: reconnecting the parent must not discard broker data. */
static struct {
  int reader, writer;
  uint32_t timeout;
  unsigned char header[4];
  size_t header_used, body_used;
  lean_object *body;
} queue = {.reader = -1, .writer = -1};
static int detached_broker;

static int64_t now_ms(void) {
  struct timespec ts;
  if (clock_gettime(CLOCK_MONOTONIC, &ts) != 0) return -1;
  return (int64_t)ts.tv_sec * 1000 + ts.tv_nsec / 1000000;
}
static int64_t deadline_new(void) {
  int64_t now = now_ms();
  return now < 0 ? -1 : now + (int64_t)connection.timeout * 1000;
}
static int remaining(int64_t deadline) {
  int64_t now = now_ms();
  if (now < 0) return -1;
  if (now >= deadline) return 0;
  int64_t n = deadline - now;
  return n > INT_MAX ? INT_MAX : (int)n;
}
/* 1 ready, 0 no immediate readiness, -1 error/timeout. HUP is readiness:
 * recv/SSL_read must still consume buffered bytes before reporting EOF. */
static int wait_fd(int fd, short events, int wait, int64_t deadline) {
  for (;;) {
    int ms = remaining(deadline);
    if (ms < 0) return -1;
    if (wait && ms == 0) { errno = ETIMEDOUT; return -1; }
    struct pollfd pfd = {.fd = fd, .events = events};
    int rc = poll(&pfd, 1, wait ? ms : 0);
    if (rc < 0) {
      if (errno == EINTR) {
        if (!wait) return 0;
        continue;
      }
      return -1;
    }
    if (rc == 0) {
      if (!wait) return 0;
      continue;
    }
    if (pfd.revents & POLLNVAL) { errno = EBADF; return -1; }
    if (pfd.revents & (events | POLLERR | POLLHUP)) return 1;
  }
}
static int cloexec(int fd) {
  int flags = fcntl(fd, F_GETFD);
  return flags < 0 ? -1 : fcntl(fd, F_SETFD, flags | FD_CLOEXEC);
}
static int nonblocking(int fd) {
  int flags = fcntl(fd, F_GETFL);
  return flags < 0 ? -1 : fcntl(fd, F_SETFL, flags | O_NONBLOCK);
}
static void reset(void) {
  int saved = errno;
  connection.relay = 0;
  /* No SSL_shutdown: close must neither block nor emit copied child records. */
  if (connection.ssl) connection.api.ssl_free(connection.ssl);
  if (connection.ctx) connection.api.ctx_free(connection.ctx);
  if (connection.fd >= 0) close(connection.fd);
  if (connection.body) lean_dec(connection.body);
  if (connection.ssl_lib) dlclose(connection.ssl_lib);
  if (connection.crypto_lib) dlclose(connection.crypto_lib);
  memset(&connection, 0, sizeof connection);
  connection.fd = -1;
  errno = saved;
}
static lean_obj_res failure(const char *operation) {
  int error = errno ? errno : EIO;
  reset();
  char message[512];
  if (error == ENODATA && strcmp(operation, "receive") == 0)
    snprintf(message, sizeof message, "lost connection to log server");
  else
    snprintf(message, sizeof message, "log server %s: %s", operation, strerror(error));
  return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(message)));
}

/* getaddrinfo has no portable deadline. Isolate it in a resolver child instead
 * of abandoning a thread (and its credentials/resources) after a timeout.
 * Only fixed-size socket addresses cross this private pipe, never pointers. */
struct resolved_address {
  int family, socktype, protocol;
  socklen_t length;
  struct sockaddr_storage address;
};
struct address_node {
  struct resolved_address value;
  struct address_node *next;
};
static int resolver_write(int fd, const struct resolved_address *address) {
  const unsigned char *p = (const unsigned char *)address;
  size_t left = sizeof *address;
  while (left) {
    ssize_t n = write(fd, p, left);
    if (n < 0 && errno == EINTR) continue;
    if (n <= 0) return -1;
    p += n;
    left -= (size_t)n;
  }
  return 0;
}
static void resolver_child(int fd, const char *host, const char *service) {
  struct sigaction action;
  memset(&action, 0, sizeof action);
  action.sa_handler = SIG_IGN;
  sigemptyset(&action.sa_mask);
  if (sigaction(SIGPIPE, &action, NULL) != 0) _exit(1);
  struct addrinfo hints, *result = NULL;
  memset(&hints, 0, sizeof hints);
  hints.ai_family = AF_UNSPEC;
  hints.ai_socktype = SOCK_STREAM;
  hints.ai_protocol = IPPROTO_TCP;
  int rc = getaddrinfo(host, service, &hints, &result);
  if (rc != 0) _exit(1);
  for (const struct addrinfo *ai = result; ai; ai = ai->ai_next) {
    if ((ai->ai_family != AF_INET && ai->ai_family != AF_INET6) ||
        ai->ai_addrlen > sizeof(struct sockaddr_storage)) continue;
    struct resolved_address address;
    memset(&address, 0, sizeof address);
    address.family = ai->ai_family;
    address.socktype = ai->ai_socktype;
    address.protocol = ai->ai_protocol;
    address.length = ai->ai_addrlen;
    memcpy(&address.address, ai->ai_addr, ai->ai_addrlen);
    if (resolver_write(fd, &address) != 0) { freeaddrinfo(result); _exit(1); }
  }
  freeaddrinfo(result);
  struct resolved_address end;
  memset(&end, 0, sizeof end);
  int status = resolver_write(fd, &end);
  close(fd);
  _exit(status == 0 ? 0 : 1);
}
static void addresses_free(struct address_node *addresses) {
  while (addresses) {
    struct address_node *next = addresses->next;
    free(addresses);
    addresses = next;
  }
}
static struct address_node *resolve(const char *host, const char *service, int64_t deadline) {
  int pipes[2];
  if (pipe(pipes) != 0) return NULL;
  if (cloexec(pipes[0]) != 0 || cloexec(pipes[1]) != 0 || nonblocking(pipes[0]) != 0) {
    int saved = errno;
    close(pipes[0]); close(pipes[1]); errno = saved;
    return NULL;
  }
  pid_t pid = fork();
  if (pid == 0) {
    close(pipes[0]);
    resolver_child(pipes[1], host, service);
  }
  int saved = errno;
  close(pipes[1]);
  if (pid < 0) { close(pipes[0]); errno = saved; return NULL; }
  struct address_node *first = NULL, **last = &first;
  int complete = 0;
  for (;;) {
    struct resolved_address address;
    size_t used = 0;
    while (used < sizeof address) {
      if (wait_fd(pipes[0], POLLIN, 1, deadline) < 0) goto finished;
      ssize_t n = read(pipes[0], (unsigned char *)&address + used, sizeof address - used);
      if (n < 0 && (errno == EINTR || errno == EAGAIN)) continue;
      if (n <= 0) { if (!n) errno = EHOSTUNREACH; goto finished; }
      used += (size_t)n;
    }
    if (address.length == 0) { complete = 1; break; }
    struct address_node *node = malloc(sizeof *node);
    if (!node) goto finished;
    node->value = address;
    node->next = NULL;
    *last = node;
    last = &node->next;
  }
finished:
  saved = errno;
  /* Even a completed child is stopped before reaping: never wait unboundedly
   * for resolver cleanup or an NSS module's exit hook. */
  kill(pid, SIGKILL);
  close(pipes[0]);
  while (waitpid(pid, NULL, 0) < 0 && errno == EINTR) {}
  if (!complete) { addresses_free(first); errno = saved; return NULL; }
  if (!first) errno = EHOSTUNREACH;
  return first;
}

static int connect_addresses(const struct address_node *addresses, int keepalive, int64_t deadline) {
  int last_error = EHOSTUNREACH;
  for (const struct address_node *node = addresses; node; node = node->next) {
    int ms = remaining(deadline);
    if (ms <= 0) { if (!ms) errno = ETIMEDOUT; return -1; }
    const struct resolved_address *address = &node->value;
    int fd = socket(address->family, address->socktype, address->protocol);
    if (fd < 0) { last_error = errno; continue; }
    int enabled = keepalive != 0;
    if (cloexec(fd) != 0 || nonblocking(fd) != 0 ||
        setsockopt(fd, SOL_SOCKET, SO_KEEPALIVE, &enabled, sizeof enabled) != 0) {
      last_error = errno; close(fd); continue;
    }
#ifdef SO_NOSIGPIPE
    enabled = 1;
    if (setsockopt(fd, SOL_SOCKET, SO_NOSIGPIPE, &enabled, sizeof enabled) != 0) {
      last_error = errno; close(fd); continue;
    }
#endif
    int rc = connect(fd, (const struct sockaddr *)&address->address, address->length);
    if (rc < 0 && (errno == EINPROGRESS || errno == EINTR || errno == EALREADY)) {
      rc = wait_fd(fd, POLLOUT, 1, deadline);
      if (rc > 0) {
        int error = 0;
        socklen_t length = sizeof error;
        rc = getsockopt(fd, SOL_SOCKET, SO_ERROR, &error, &length);
        if (rc == 0 && error) { errno = error; rc = -1; }
      }
    }
    if (rc == 0) { connection.fd = fd; return 0; }
    last_error = errno;
    close(fd);
  }
  errno = last_error;
  return -1;
}

static void *load_library(const char *soname, const char *dylib) {
  void *handle = dlopen(soname, RTLD_NOW | RTLD_LOCAL);
#ifdef __APPLE__
  if (!handle) handle = dlopen(dylib, RTLD_NOW | RTLD_LOCAL);
#else
  (void)dylib;
#endif
  return handle;
}
static int tls_load(void) {
  connection.crypto_lib = load_library("libcrypto.so.3", "libcrypto.3.dylib");
  connection.ssl_lib = load_library("libssl.so.3", "libssl.3.dylib");
  if (!connection.crypto_lib || !connection.ssl_lib) { errno = ENOSYS; return -1; }
  struct tls_api *api = &connection.api;
  const struct { const char *name; void *slot; int crypto; } symbols[] = {
    {"TLS_client_method", &api->client_method, 0},
    {"SSL_CTX_new", &api->ctx_new, 0},
    {"SSL_CTX_free", &api->ctx_free, 0},
    {"SSL_CTX_ctrl", &api->ctx_ctrl, 0},
    {"SSL_CTX_set_verify", &api->ctx_set_verify, 0},
    {"SSL_CTX_load_verify_locations", &api->ctx_load_ca, 0},
    {"SSL_CTX_set_default_verify_paths", &api->ctx_default_ca, 0},
    {"SSL_CTX_use_certificate_chain_file", &api->ctx_use_cert, 0},
    {"SSL_CTX_use_PrivateKey_file", &api->ctx_use_key, 0},
    {"SSL_CTX_check_private_key", &api->ctx_check_key, 0},
    {"SSL_new", &api->ssl_new, 0},
    {"SSL_free", &api->ssl_free, 0},
    {"SSL_set_fd", &api->ssl_set_fd, 0},
    {"SSL_ctrl", &api->ssl_ctrl, 0},
    {"SSL_get1_peer_certificate", &api->ssl_peer_cert, 0},
    {"SSL_get_verify_result", &api->ssl_verify_result, 0},
    {"SSL_connect", &api->ssl_connect, 0},
    {"SSL_read", &api->ssl_read, 0},
    {"SSL_write", &api->ssl_write, 0},
    {"SSL_get_error", &api->ssl_error, 0},
    {"X509_check_host", &api->cert_host, 1},
    {"X509_check_ip", &api->cert_ip, 1},
    {"X509_get_ext_by_NID", &api->cert_ext_by_nid, 1},
    {"X509_free", &api->cert_free, 1},
    {"ERR_clear_error", &api->clear_error, 1},
    {"ERR_get_error", &api->get_error, 1},
    {"ERR_reason_error_string", &api->reason_error, 1}
  };
  for (size_t i = 0; i < sizeof symbols / sizeof symbols[0]; i++) {
    void *symbol = dlsym(symbols[i].crypto ? connection.crypto_lib : connection.ssl_lib,
        symbols[i].name);
    if (!symbol) { errno = ENOSYS; return -1; }
    memcpy(symbols[i].slot, &symbol, sizeof symbol);
  }
  return 0;
}

/* OpenSSL's socket BIO can write during reads and handshakes, too. Block SIGPIPE
 * only in this thread, consume only a newly pending signal, then restore the
 * original mask. Unlike SIG_IGN this cannot alter the executed command's ABI. */
static int tls_step(int operation, void *buf, size_t len, short *want) {
  sigset_t blocked, old, pending;
  sigemptyset(&blocked);
  sigaddset(&blocked, SIGPIPE);
  int error = pthread_sigmask(SIG_BLOCK, &blocked, &old);
  if (error) { errno = error; return -1; }
  if (sigpending(&pending) != 0) {
    int saved = errno;
    pthread_sigmask(SIG_SETMASK, &old, NULL);
    errno = saved;
    return -1;
  }
  int had_pending = sigismember(&pending, SIGPIPE);
  connection.api.clear_error();
  errno = 0;
  int rc;
  if (operation == 2) rc = connection.api.ssl_connect(connection.ssl);
  else if (operation == 1) rc = connection.api.ssl_write(connection.ssl, buf, (int)len);
  else rc = connection.api.ssl_read(connection.ssl, buf, (int)len);
  int saved = errno;
  connection.tls_errno = saved;
  int ssl_error = rc > 0 ? 0 : connection.api.ssl_error(connection.ssl, rc);
  if (!had_pending && sigpending(&pending) == 0 && sigismember(&pending, SIGPIPE)) {
    int signal_number;
    sigwait(&blocked, &signal_number);
  }
  error = pthread_sigmask(SIG_SETMASK, &old, NULL);
  if (error) { errno = error; return -1; }
  errno = saved;
  if (rc > 0) return rc;
  if (ssl_error == 2 || ssl_error == 3) { /* SSL_ERROR_WANT_READ / WANT_WRITE */
    *want = ssl_error == 2 ? POLLIN : POLLOUT;
    return 0;
  }
  if (ssl_error == 5 && saved == EINTR) { /* SSL_ERROR_SYSCALL */
    *want = 0;
    return 0;
  }
  errno = ssl_error == 6 ? ENODATA : ssl_error == 5 && saved ? saved : EPROTO;
  return -1;
}
/* sudo's validate_hostname(..., resolve=0): match a SAN hostname OR the
 * connected peer's SAN IP; only an absent SAN permits subject CN fallback.
 * Chain verification remains mandatory in SSL_connect. No application bytes
 * are sent until this additional identity check succeeds. */
static int tls_verify_identity(const char *host) {
  struct sockaddr_storage peer;
  socklen_t peer_length = sizeof peer;
  if (getpeername(connection.fd, (struct sockaddr *)&peer, &peer_length) != 0) return -1;
  const unsigned char *address;
  size_t address_length;
  if (peer.ss_family == AF_INET && peer_length >= sizeof(struct sockaddr_in)) {
    address = (const unsigned char *)&((const struct sockaddr_in *)&peer)->sin_addr;
    address_length = sizeof(struct in_addr);
  } else if (peer.ss_family == AF_INET6 && peer_length >= sizeof(struct sockaddr_in6)) {
    address = (const unsigned char *)&((const struct sockaddr_in6 *)&peer)->sin6_addr;
    address_length = sizeof(struct in6_addr);
  } else { errno = EAFNOSUPPORT; return -1; }
  struct tls_api *api = &connection.api;
  X509 *cert = api->ssl_peer_cert(connection.ssl);
  if (!cert) { errno = EACCES; return -1; }
  size_t host_length = strlen(host);
  if (host_length && host[host_length - 1] == '.') --host_length;
  unsigned int flags = 4; /* X509_CHECK_FLAG_NO_PARTIAL_WILDCARDS */
  /* NID_subject_alt_name = 85, X509_CHECK_FLAG_NEVER_CHECK_SUBJECT = 0x20.
   * In particular, an IP-only SAN must not enable CN hostname fallback. */
  if (api->cert_ext_by_nid(cert, 85, -1) >= 0) flags |= 0x20;
  int match = host_length ? api->cert_host(cert, host, host_length, flags, NULL) : -1;
  if (match == 0) match = api->cert_ip(cert, address, address_length, 0);
  api->cert_free(cert);
  if (match != 1) { errno = EACCES; return -1; }
  return 0;
}

static int tls_start(const char *host, int verify, const char *ca, const char *cert,
    const char *key, int64_t deadline) {
  if (tls_load() != 0) return -1;
  struct tls_api *api = &connection.api;
  errno = EPROTO;
  connection.ctx = api->ctx_new(api->client_method());
  if (!connection.ctx) return -1;
  /* SSL_CTRL_SET_MIN_PROTO_VERSION = 123, TLS1_2_VERSION = 0x0303. */
  if (api->ctx_ctrl(connection.ctx, 123, 0x0303, NULL) != 1) return -1;
  api->ctx_set_verify(connection.ctx, verify ? 1 : 0, NULL);
  if (verify) {
    if (*ca) {
      if (api->ctx_load_ca(connection.ctx, ca, NULL) != 1) return -1;
    } else if (api->ctx_default_ca(connection.ctx) != 1) return -1;
  }
  if (*cert) {
    if (api->ctx_use_cert(connection.ctx, cert) != 1 ||
        api->ctx_use_key(connection.ctx, *key ? key : cert, 1) != 1 ||
        api->ctx_check_key(connection.ctx) != 1) return -1;
  }
  connection.ssl = api->ssl_new(connection.ctx);
  if (!connection.ssl || api->ssl_set_fd(connection.ssl, connection.fd) != 1) return -1;
  struct in6_addr ip;
  int numeric = inet_pton(AF_INET, host, &ip) == 1 || inet_pton(AF_INET6, host, &ip) == 1;
  /* SSL_CTRL_SET_TLSEXT_HOSTNAME = 55; host_name = 0. No SNI for IP literals. */
  if (!numeric && api->ssl_ctrl(connection.ssl, 55, 0, (void *)host) != 1) return -1;
  for (;;) {
    int ms = remaining(deadline);
    if (ms <= 0) { if (!ms) errno = ETIMEDOUT; return -1; }
    short want = 0;
    int rc = tls_step(2, NULL, 0, &want);
    if (rc > 0) break;
    if (rc < 0) return -1;
    if (want && wait_fd(connection.fd, want, 1, deadline) < 0) return -1;
  }
  if (verify && api->ssl_verify_result(connection.ssl) != 0) { errno = EACCES; return -1; }
  if (verify && tls_verify_identity(host) != 0) return -1;
  return 0;
}

/* Positive byte count, zero for a nonblocking partial frame, or -1 on error.
 * SSL retries retain exactly the same buffer/length until progress is made. */
static ssize_t transfer(void *buf, size_t len, int writing, int wait, int64_t deadline) {
  for (;;) {
    int ms = remaining(deadline);
    if (ms < 0) return -1;
    if (ms == 0 && wait) { errno = ETIMEDOUT; return -1; }
    short want = writing ? POLLOUT : POLLIN;
    ssize_t rc;
    if (connection.ssl) {
      rc = tls_step(writing, buf, len, &want);
      if (rc < 0) return -1;
    } else {
      if (writing) {
#ifdef MSG_NOSIGNAL
        rc = send(connection.fd, buf, len, MSG_NOSIGNAL);
#else
        rc = send(connection.fd, buf, len, 0);
#endif
      } else rc = recv(connection.fd, buf, len, 0);
      if (rc == 0) { errno = ENODATA; return -1; }
      if (rc < 0) {
        if (errno == EINTR) {
          if (!wait || ms == 0) return 0;
          continue;
        }
        if (errno != EAGAIN && errno != EWOULDBLOCK) return -1;
      }
    }
    if (rc > 0) return rc;
    if (!want) {
      if (!wait || ms == 0) return 0;
      continue;
    }
    int ready = wait_fd(connection.fd, want, wait, deadline);
    if (ready <= 0) return ready;
    if (!wait && ms == 0) return 0;
  }
}

LEAN_EXPORT lean_obj_res leansudo_logsrv_clock(lean_obj_arg world) {
  (void)world;
  struct timespec ts;
  int rc;
  do { rc = clock_gettime(CLOCK_MONOTONIC, &ts); } while (rc != 0 && errno == EINTR);
  if (rc != 0 || ts.tv_sec < 0 || ts.tv_nsec < 0 || ts.tv_nsec >= 1000000000L ||
      (uint64_t)ts.tv_sec > (UINT64_MAX - (uint64_t)ts.tv_nsec) / UINT64_C(1000000000))
    return lean_io_result_mk_error(lean_mk_io_user_error(
        lean_mk_string("unable to read log server monotonic clock")));
  uint64_t ns = (uint64_t)ts.tv_sec * UINT64_C(1000000000) + (uint64_t)ts.tv_nsec;
  return lean_io_result_mk_ok(lean_uint64_to_nat(ns));
}

static lean_obj_res tls_failure(const char *host, const char *port) {
  int error = errno;
  const char *reason = NULL;
  if (connection.api.get_error && connection.api.reason_error)
    reason = connection.api.reason_error(connection.api.get_error());
  if (!reason && error == EACCES) reason = "certificate verify failed";
  if (!reason) reason = strerror(error);
  char message[1024];
  snprintf(message, sizeof message,
      "TLS connection to %s:%s failed: %s\nTLS %s was unsuccessful: %s",
      host, port, reason, connection.ssl ? "handshake" : "initialization",
      strerror(connection.tls_errno));
  reset();
  return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(message)));
}

LEAN_EXPORT lean_obj_res leansudo_logsrv_connect(b_lean_obj_arg host,
    b_lean_obj_arg service, uint8_t tls, uint32_t timeout, uint8_t keepalive,
    uint8_t verify, b_lean_obj_arg ca, b_lean_obj_arg cert, b_lean_obj_arg key,
    lean_obj_arg world) {
  (void)world;
  reset();
  connection.timeout = timeout;
  int64_t deadline = deadline_new();
  if (deadline < 0) return failure("clock");
  struct address_node *addresses = resolve(lean_string_cstr(host), lean_string_cstr(service), deadline);
  if (!addresses) return failure("resolve");
  int rc = connect_addresses(addresses, keepalive, deadline);
  int saved = errno;
  addresses_free(addresses);
  errno = saved;
  if (rc != 0) return failure("connect");
  if (tls && tls_start(lean_string_cstr(host), verify, lean_string_cstr(ca),
      lean_string_cstr(cert), lean_string_cstr(key), deadline) != 0)
    return tls_failure(lean_string_cstr(host), lean_string_cstr(service));
  return lean_io_result_mk_ok(lean_box(0));
}
LEAN_EXPORT lean_obj_res leansudo_logsrv_send(b_lean_obj_arg bytes, lean_obj_arg world) {
  (void)world;
  if (connection.fd < 0) { errno = ENOTCONN; return failure("send"); }
  size_t len = lean_sarray_size(bytes);
  if (len > LOGSRV_MAX_FRAME) { errno = EMSGSIZE; return failure("send"); }
  uint32_t header = htonl((uint32_t)len);
  int64_t deadline = deadline_new();
  if (deadline < 0) return failure("clock");
  const unsigned char *parts[2] = {(const unsigned char *)&header, lean_sarray_cptr(bytes)};
  size_t lengths[2] = {sizeof header, len};
  for (size_t i = 0; i < 2; i++) {
    size_t used = 0;
    while (used < lengths[i]) {
      ssize_t n = transfer((void *)(parts[i] + used), lengths[i] - used, 1, 1, deadline);
      if (n < 0) return failure("send");
      used += (size_t)n;
    }
  }
  return lean_io_result_mk_ok(lean_box(0));
}
LEAN_EXPORT lean_obj_res leansudo_logsrv_receive(uint8_t wait, lean_obj_arg world) {
  (void)world;
  if (connection.fd < 0) { errno = ENOTCONN; return failure("receive"); }
  int64_t deadline = deadline_new();
  if (deadline < 0) return failure("clock");
  while (connection.header_used < sizeof connection.header) {
    ssize_t n = transfer(connection.header + connection.header_used,
        sizeof connection.header - connection.header_used, 0, wait, deadline);
    if (n < 0) return failure("receive");
    if (!n) return lean_io_result_mk_ok(lean_box(0));
    connection.header_used += (size_t)n;
  }
  if (!connection.body) {
    uint32_t length;
    memcpy(&length, connection.header, sizeof length);
    length = ntohl(length);
    if (length > LOGSRV_MAX_FRAME) { errno = EMSGSIZE; return failure("receive"); }
    connection.body = lean_alloc_sarray(1, length, length);
  }
  size_t length = lean_sarray_size(connection.body);
  while (connection.body_used < length) {
    ssize_t n = transfer(lean_sarray_cptr(connection.body) + connection.body_used,
        length - connection.body_used, 0, wait, deadline);
    if (n < 0) return failure("receive");
    if (!n) return lean_io_result_mk_ok(lean_box(0));
    connection.body_used += (size_t)n;
  }
  lean_object *some = lean_alloc_ctor(1, 1, 0);
  lean_ctor_set(some, 0, connection.body);
  connection.body = NULL;
  connection.header_used = connection.body_used = 0;
  return lean_io_result_mk_ok(some);
}
LEAN_EXPORT lean_obj_res leansudo_logsrv_close(lean_obj_arg world) {
  (void)world;
  reset();
  return lean_io_result_mk_ok(lean_box(0));
}
LEAN_EXPORT lean_obj_res leansudo_logsrv_relay(uint32_t mask, lean_obj_arg world) {
  (void)world;
  if (mask & ~UINT32_C(31)) { errno = EINVAL; return failure("relay"); }
  if (mask && connection.fd < 0) { errno = ENOTCONN; return failure("relay"); }
  connection.relay = mask;
  return lean_io_result_mk_ok(lean_box(0));
}
int ls_logsrv_active(void) { return connection.relay != 0; }
int ls_logsrv_stream(int stream) {
  return stream >= 0 && stream < 5 && (connection.relay & (UINT32_C(1) << stream)) != 0;
}
int ls_logsrv_network_fd(void) { return connection.relay ? connection.fd : -1; }
/* Keep Lean's policy error intact while the syscall relay unwinds and reaps the
 * command; replacing it with errno would lose the callback's diagnostic. */
static lean_object *callback_error;
lean_obj_res ls_logsrv_take_error(void) {
  lean_object *result = callback_error;
  callback_error = NULL;
  return result;
}
static int callback_status(lean_obj_res result) {
  if (lean_io_result_is_ok(result)) {
    lean_dec(result);
    return 0;
  }
  if (callback_error) lean_dec(callback_error);
  callback_error = result;
  errno = EIO;
  reset();
  return -1;
}
int ls_logsrv_poll(void) {
  if (!connection.relay) return 0;
  lean_object *result = leansudo_logsrv_poll(lean_box(0));
  return callback_status(result);
}
int ls_logsrv_event(int event, const void *buf, size_t len, unsigned a, unsigned b) {
  if (!ls_logsrv_active()) return 0;
  if (event >= 0 && event < 5 && !ls_logsrv_stream(event)) return 0;
  if (event < 0 || (len && !buf)) { errno = EINVAL; reset(); return -1; }
  lean_object *data = lean_alloc_sarray(1, len, len);
  if (len) memcpy(lean_sarray_cptr(data), buf, len);
  lean_object *result = leansudo_logsrv_io_event((uint32_t)event, data, a, b, lean_box(0));
  return callback_status(result);
}

static void queue_reset(void) {
  int saved = errno;
  if (queue.reader >= 0) close(queue.reader);
  if (queue.writer >= 0) close(queue.writer);
  if (queue.body) lean_dec(queue.body);
  memset(&queue, 0, sizeof queue);
  queue.reader = queue.writer = -1;
  errno = saved;
}
static lean_obj_res queue_failure(const char *operation) {
  int error = errno ? errno : EIO;
  /* Poison a partial send for every inherited copy of this endpoint. Merely
   * closing the broker's descriptor would leave the parent's writer alive. */
  if (queue.writer >= 0) shutdown(queue.writer, SHUT_RDWR);
  queue_reset();
  char message[512];
  snprintf(message, sizeof message, "log server queue %s: %s", operation, strerror(error));
  return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(message)));
}
LEAN_EXPORT lean_obj_res leansudo_logsrv_queue_init(lean_obj_arg world) {
  (void)world;
  queue_reset();
  if (connection.fd < 0) { errno = ENOTCONN; return queue_failure("initialize"); }
  int pair[2];
  if (socketpair(AF_UNIX, SOCK_STREAM, 0, pair) != 0) return queue_failure("initialize");
  queue.reader = pair[0];
  queue.writer = pair[1];
  queue.timeout = connection.timeout;
  if (cloexec(pair[0]) != 0 || cloexec(pair[1]) != 0 ||
      nonblocking(pair[0]) != 0 || nonblocking(pair[1]) != 0)
    return queue_failure("initialize");
#ifdef SO_NOSIGPIPE
  int enabled = 1;
  if (setsockopt(queue.writer, SOL_SOCKET, SO_NOSIGPIPE, &enabled, sizeof enabled) != 0)
    return queue_failure("initialize");
#endif
  return lean_io_result_mk_ok(lean_box(0));
}
LEAN_EXPORT lean_obj_res leansudo_logsrv_queue_send(b_lean_obj_arg bytes, lean_obj_arg world) {
  (void)world;
  if (queue.writer < 0) { errno = ENOTCONN; return queue_failure("send"); }
  size_t len = lean_sarray_size(bytes);
  if (len > LOGSRV_MAX_FRAME) { errno = EMSGSIZE; return queue_failure("send"); }
  int64_t now = now_ms();
  if (now < 0) return queue_failure("clock");
  int64_t deadline = now + (int64_t)queue.timeout * 1000;
  uint32_t header = htonl((uint32_t)len);
  const unsigned char *parts[2] = {(const unsigned char *)&header, lean_sarray_cptr(bytes)};
  size_t lengths[2] = {sizeof header, len};
  for (size_t i = 0; i < 2; i++) {
    size_t used = 0;
    while (used < lengths[i]) {
      int ms = remaining(deadline);
      if (ms <= 0) { if (!ms) errno = ETIMEDOUT; return queue_failure("send"); }
#ifdef MSG_NOSIGNAL
      ssize_t n = send(queue.writer, parts[i] + used, lengths[i] - used, MSG_NOSIGNAL);
#else
      ssize_t n = send(queue.writer, parts[i] + used, lengths[i] - used, 0);
#endif
      if (n < 0 && errno == EINTR) continue;
      if (n < 0 && (errno == EAGAIN || errno == EWOULDBLOCK)) {
        if (wait_fd(queue.writer, POLLOUT, 1, deadline) < 0) return queue_failure("send");
        continue;
      }
      if (n <= 0) { if (!n) errno = EPIPE; return queue_failure("send"); }
      used += (size_t)n;
    }
  }
  return lean_io_result_mk_ok(lean_box(0));
}
LEAN_EXPORT lean_obj_res leansudo_logsrv_queue_close(lean_obj_arg world) {
  (void)world;
  queue_reset();
  return lean_io_result_mk_ok(lean_box(0));
}
int ls_logsrv_queue_fd(void) { return queue.reader; }

/* No waiting here: the exec monitor owns readiness and command supervision. */
static int queue_read(void *buf, size_t len, size_t *used) {
  while (*used < len) {
    ssize_t n = recv(queue.reader, (unsigned char *)buf + *used, len - *used, 0);
    if (n < 0 && (errno == EAGAIN || errno == EWOULDBLOCK || errno == EINTR)) return 0;
    if (n <= 0) { if (!n) errno = ECONNRESET; return -1; }
    *used += (size_t)n;
  }
  return 1;
}
int ls_logsrv_dispatch(void) {
  if (queue.reader < 0) return 0;
  for (;;) {
    int rc = queue_read(queue.header, sizeof queue.header, &queue.header_used);
    if (rc == 0) return 0;
    if (rc < 0) { queue_reset(); return -1; }
    if (!queue.body) {
      uint32_t length;
      memcpy(&length, queue.header, sizeof length);
      length = ntohl(length);
      if (length > LOGSRV_MAX_FRAME) { errno = EMSGSIZE; queue_reset(); return -1; }
      queue.body = lean_alloc_sarray(1, length, length);
    }
    rc = queue_read(lean_sarray_cptr(queue.body), lean_sarray_size(queue.body), &queue.body_used);
    if (rc == 0) return 0;
    if (rc < 0) { queue_reset(); return -1; }
    lean_object *body = queue.body;
    queue.body = NULL;
    queue.header_used = queue.body_used = 0;
    lean_object *result = leansudo_logsrv_subcommand_wire(body, lean_box(0));
    if (callback_status(result)) { queue_reset(); return -1; }
    /* Lean may close the queue as part of its failure policy. */
    if (queue.reader < 0) return 0;
  }
}
LEAN_EXPORT lean_obj_res leansudo_logsrv_is_broker(lean_obj_arg world) {
  (void)world;
  return lean_io_result_mk_ok(lean_box(detached_broker != 0));
}
void ls_logsrv_detach_child(void) {
  detached_broker = 1;
  if (connection.fd >= 0) close(connection.fd);
  connection.fd = -1;
  connection.relay = 0;
  if (queue.reader >= 0) close(queue.reader);
  queue.reader = -1;
}
void ls_logsrv_child_close(void) {
  /* Child-side descriptor drop only: no TLS activity or Lean runtime calls
   * between fork and exec. The parent's connection and buffers are untouched. */
  if (connection.fd >= 0) close(connection.fd);
  connection.fd = -1;
  connection.relay = 0;
  if (queue.reader >= 0) close(queue.reader);
  if (queue.writer >= 0) close(queue.writer);
  queue.reader = queue.writer = -1;
}
