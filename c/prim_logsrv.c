#ifndef _GNU_SOURCE
#define _GNU_SOURCE
#endif
#include <lean/lean.h>
#include <arpa/inet.h>
#include <dlfcn.h>
#include <errno.h>
#include <fcntl.h>
#include <limits.h>
#include <netdb.h>
#include <poll.h>
#include <signal.h>
#include <stddef.h>
#include <stdint.h>
#include <string.h>
#include <sys/socket.h>
#include <time.h>
#include <unistd.h>

enum {
  LS_SSL_FILETYPE_PEM = 1,
  LS_SSL_CTRL_SET_TLSEXT_HOSTNAME = 55,
  LS_TLSEXT_NAMETYPE_HOST_NAME = 0,
  LS_NID_SUBJECT_ALT_NAME = 85
};

#define LOG_CONSTANT(name, value) \
  LEAN_EXPORT uint32_t ls_logprim_##name(lean_obj_arg unit) { (void)unit; return (value); }
LOG_CONSTANT(eintr, EINTR)
LOG_CONSTANT(eio, EIO)
LOG_CONSTANT(etimedout, ETIMEDOUT)
LOG_CONSTANT(ebadf, EBADF)
LOG_CONSTANT(enodata, ENODATA)
LOG_CONSTANT(eproto, EPROTO)
LOG_CONSTANT(enotconn, ENOTCONN)
LOG_CONSTANT(eagain, EAGAIN)
LOG_CONSTANT(ewouldblock, EWOULDBLOCK)
LOG_CONSTANT(emsgsize, EMSGSIZE)
LOG_CONSTANT(epipe, EPIPE)
LOG_CONSTANT(ehostunreach, EHOSTUNREACH)
LOG_CONSTANT(einprogress, EINPROGRESS)
LOG_CONSTANT(ealready, EALREADY)
LOG_CONSTANT(enosys, ENOSYS)
LOG_CONSTANT(eacces, EACCES)
LOG_CONSTANT(eafnosupport, EAFNOSUPPORT)
LOG_CONSTANT(einval, EINVAL)
LOG_CONSTANT(getfd, F_GETFD)
LOG_CONSTANT(setfd, F_SETFD)
LOG_CONSTANT(cloexec, FD_CLOEXEC)
LOG_CONSTANT(getfl, F_GETFL)
LOG_CONSTANT(setfl, F_SETFL)
LOG_CONSTANT(nonblock, O_NONBLOCK)
LOG_CONSTANT(pollin, POLLIN)
LOG_CONSTANT(pollout, POLLOUT)
LOG_CONSTANT(pollnval, POLLNVAL)
LOG_CONSTANT(pollerr, POLLERR)
LOG_CONSTANT(pollhup, POLLHUP)
LOG_CONSTANT(inet, AF_INET)
LOG_CONSTANT(inet6, AF_INET6)
LOG_CONSTANT(unspec, AF_UNSPEC)
LOG_CONSTANT(stream, SOCK_STREAM)
LOG_CONSTANT(tcp, IPPROTO_TCP)
LOG_CONSTANT(sigpipe, SIGPIPE)
LOG_CONSTANT(sockaddrStorageSize, sizeof(struct sockaddr_storage))
LOG_CONSTANT(sigkill, SIGKILL)
LOG_CONSTANT(intMax, INT_MAX)
LOG_CONSTANT(ipv4Offset, offsetof(struct sockaddr_in, sin_addr))
LOG_CONSTANT(ipv4Size, sizeof(struct in_addr))
LOG_CONSTANT(sockaddr4Size, sizeof(struct sockaddr_in))
LOG_CONSTANT(ipv6Offset, offsetof(struct sockaddr_in6, sin6_addr))
LOG_CONSTANT(ipv6Size, sizeof(struct in6_addr))
LOG_CONSTANT(sockaddr6Size, sizeof(struct sockaddr_in6))
#undef LOG_CONSTANT

static lean_object *pair(lean_object *a, lean_object *b) {
  lean_object *value = lean_alloc_ctor(0, 2, 0);
  lean_ctor_set(value, 0, a);
  lean_ctor_set(value, 1, b);
  return value;
}
static lean_object *result(uint32_t error, lean_object *value) {
  return pair(lean_box_uint32(error), value);
}
static lean_object *integer(int value) {
  int error = value < 0 ? errno : 0;
  return result(error, lean_box_uint32((uint32_t)value));
}
LEAN_EXPORT lean_obj_res ls_logprim_clock(void) {
  struct timespec ts = {0};
  int rc = clock_gettime(CLOCK_MONOTONIC, &ts);
  int error = rc < 0 ? errno : 0;
  return result(error, pair(lean_box_uint64(ts.tv_sec), lean_box_uint64(ts.tv_nsec)));
}
LEAN_EXPORT lean_obj_res ls_logprim_error(uint32_t error) {
  char buffer[256] = {0};
#if defined(__GLIBC__)
  const char *message = strerror_r((int)error, buffer, sizeof buffer);
  return lean_mk_string_from_bytes(message, strnlen(message, sizeof buffer - 1));
#else
  (void)strerror_r((int)error, buffer, sizeof buffer);
  return lean_mk_string(buffer);
#endif
}
LEAN_EXPORT lean_obj_res ls_logprim_gai_error(uint32_t error) {
  return lean_mk_string(gai_strerror((int)error));
}
LEAN_EXPORT lean_obj_res ls_logprim_resolve(b_lean_obj_arg host, b_lean_obj_arg service,
    uint32_t family, uint32_t kind, uint32_t protocol) {
  struct addrinfo hints = {
      .ai_family = (int)family, .ai_socktype = (int)kind, .ai_protocol = (int)protocol};
  struct addrinfo *addresses = NULL;
  int rc = getaddrinfo(lean_string_cstr(host), lean_string_cstr(service), &hints, &addresses);
  return result((uint32_t)rc, lean_box_uint64((uintptr_t)addresses));
}
LEAN_EXPORT lean_obj_res ls_logprim_address(uint64_t node) {
  const struct addrinfo *address = (const struct addrinfo *)(uintptr_t)node;
  size_t length = address->ai_addrlen > sizeof(struct sockaddr_storage)
      ? sizeof(struct sockaddr_storage) : address->ai_addrlen;
  lean_object *bytes = lean_alloc_sarray(1, length, length);
  memcpy(lean_sarray_cptr(bytes), address->ai_addr, length);
  return pair(lean_box_uint64((uintptr_t)address->ai_next),
      pair(lean_box_uint32(address->ai_family), pair(lean_box_uint32(address->ai_socktype),
      pair(lean_box_uint32(address->ai_protocol),
      pair(lean_box_uint32(address->ai_addrlen), bytes)))));
}
LEAN_EXPORT lean_obj_res ls_logprim_free_addresses(uint64_t node) {
  freeaddrinfo((struct addrinfo *)(uintptr_t)node);
  return lean_box(0);
}
LEAN_EXPORT lean_obj_res ls_logprim_socketpair(void) {
  int descriptors[2] = {-1, -1};
  int rc = socketpair(AF_UNIX, SOCK_STREAM, 0, descriptors);
  int error = rc < 0 ? errno : 0;
  return result(error, pair(lean_box_uint32((uint32_t)descriptors[0]),
      lean_box_uint32((uint32_t)descriptors[1])));
}
LEAN_EXPORT lean_obj_res ls_logprim_socket(uint32_t family, uint32_t kind, uint32_t protocol) {
  return integer(socket((int)family, (int)kind, (int)protocol));
}
LEAN_EXPORT lean_obj_res ls_logprim_fcntl(uint32_t fd, uint32_t command, uint32_t value) {
  return integer(fcntl((int)fd, (int)command, (int)value));
}
LEAN_EXPORT lean_obj_res ls_logprim_keepalive(uint32_t fd, uint8_t enabled) {
  int value = enabled;
  return integer(setsockopt((int)fd, SOL_SOCKET, SO_KEEPALIVE, &value, sizeof value));
}
LEAN_EXPORT lean_obj_res ls_logprim_connect(uint32_t fd, b_lean_obj_arg address) {
  return integer(connect((int)fd, (const struct sockaddr *)lean_sarray_cptr(address),
      lean_sarray_size(address)));
}
LEAN_EXPORT lean_obj_res ls_logprim_socket_error(uint32_t fd) {
  int value = 0;
  socklen_t length = sizeof value;
  int rc = getsockopt((int)fd, SOL_SOCKET, SO_ERROR, &value, &length);
  return result(rc < 0 ? errno : 0, lean_box_uint32((uint32_t)value));
}
LEAN_EXPORT lean_obj_res ls_logprim_close(uint32_t fd) {
  return integer(close((int)fd));
}
LEAN_EXPORT lean_obj_res ls_logprim_poll(uint32_t fd, uint32_t events, uint32_t timeout) {
  struct pollfd descriptor = {.fd = (int)fd, .events = (short)events};
  int rc = poll(&descriptor, 1, (int)timeout);
  return result(rc < 0 ? errno : 0, lean_box_uint32((uint32_t)descriptor.revents));
}
LEAN_EXPORT lean_obj_res ls_logprim_send(uint32_t fd, b_lean_obj_arg bytes,
    size_t offset, size_t count) {
  size_t size = lean_sarray_size(bytes);
  if (offset > size || count > size - offset)
    return result(EINVAL, lean_box_uint64((uint64_t)-1));
  ssize_t rc = send((int)fd, lean_sarray_cptr(bytes) + offset, count, MSG_NOSIGNAL);
  int error = rc < 0 ? errno : 0;
  return result(error, lean_box_uint64((uint64_t)rc));
}
LEAN_EXPORT lean_obj_res ls_logprim_recv(uint32_t fd, lean_obj_arg bytes,
    size_t offset, size_t count) {
  size_t size = lean_sarray_size(bytes);
  if (offset > size || count > size - offset)
    return result(EINVAL, pair(lean_box_uint64((uint64_t)-1), bytes));
  bytes = lean_sarray_ensure_exclusive(bytes);
  ssize_t rc = recv((int)fd, lean_sarray_cptr(bytes) + offset, count, 0);
  int error = rc < 0 ? errno : 0;
  return result(error, pair(lean_box_uint64((uint64_t)rc), bytes));
}
LEAN_EXPORT lean_obj_res ls_logprim_peer(uint32_t fd) {
  struct sockaddr_storage address = {0};
  socklen_t length = sizeof address;
  int rc = getpeername((int)fd, (struct sockaddr *)&address, &length);
  int error = rc < 0 ? errno : 0;
  lean_object *bytes = lean_alloc_sarray(1, length, length);
  memcpy(lean_sarray_cptr(bytes), &address, length);
  return result(error, pair(lean_box_uint32(address.ss_family), bytes));
}
LEAN_EXPORT uint32_t ls_logprim_numeric(uint32_t family, b_lean_obj_arg host) {
  struct in6_addr address;
  int rc = inet_pton((int)family, lean_string_cstr(host), &address);
  return (uint32_t)rc;
}
LEAN_EXPORT lean_obj_res ls_logprim_sigemptyset(void) {
  sigset_t mask = {0};
  int rc = sigemptyset(&mask);
  int error = rc < 0 ? errno : 0;
  lean_object *bytes = lean_alloc_sarray(1, sizeof mask, sizeof mask);
  memcpy(lean_sarray_cptr(bytes), &mask, sizeof mask);
  return result(error, bytes);
}
LEAN_EXPORT lean_obj_res ls_logprim_sigaddset(lean_obj_arg mask, uint32_t signal) {
  if (lean_sarray_size(mask) != sizeof(sigset_t))
    return result(EINVAL, mask);
  mask = lean_sarray_ensure_exclusive(mask);
  int rc = sigaddset((sigset_t *)lean_sarray_cptr(mask), (int)signal);
  int error = rc < 0 ? errno : 0;
  return result(error, mask);
}
LEAN_EXPORT lean_obj_res ls_logprim_sigpending(void) {
  sigset_t pending = {0};
  int rc = sigpending(&pending);
  int error = rc < 0 ? errno : 0;
  lean_object *bytes = lean_alloc_sarray(1, sizeof pending, sizeof pending);
  memcpy(lean_sarray_cptr(bytes), &pending, sizeof pending);
  return result(error, bytes);
}
LEAN_EXPORT lean_obj_res ls_logprim_sigismember(b_lean_obj_arg mask, uint32_t signal) {
  if (lean_sarray_size(mask) != sizeof(sigset_t))
    return result(EINVAL, lean_box_uint32((uint32_t)-1));
  return integer(sigismember((const sigset_t *)lean_sarray_cptr(mask), (int)signal));
}
LEAN_EXPORT lean_obj_res ls_logprim_sigtimedwait(b_lean_obj_arg mask, uint32_t timeout) {
  if (lean_sarray_size(mask) != sizeof(sigset_t))
    return result(EINVAL, lean_box_uint32((uint32_t)-1));
  struct timespec duration = {
      .tv_sec = timeout / 1000, .tv_nsec = (long)(timeout % 1000) * 1000000};
  return integer(sigtimedwait((const sigset_t *)lean_sarray_cptr(mask), NULL, &duration));
}
LEAN_EXPORT uint64_t ls_logprim_open_library(b_lean_obj_arg name) {
  void *library = dlopen(lean_string_cstr(name), RTLD_NOW | RTLD_LOCAL);
  return (uint64_t)(uintptr_t)library;
}
LEAN_EXPORT uint64_t ls_logprim_symbol(uint64_t library, b_lean_obj_arg name) {
  void *symbol = dlsym((void *)(uintptr_t)library, lean_string_cstr(name));
  return (uint64_t)(uintptr_t)symbol;
}
LEAN_EXPORT uint32_t ls_logprim_close_library(uint64_t library) {
  int rc = dlclose((void *)(uintptr_t)library);
  return (uint32_t)rc;
}
LEAN_EXPORT lean_obj_res ls_logprim_ptr0(uint64_t fn, uint32_t prior) {
  errno = prior;
  void *value = ((void *(*)(void))(uintptr_t)fn)();
  int error = errno;
  return result(error, lean_box_uint64((uintptr_t)value));
}
LEAN_EXPORT lean_obj_res ls_logprim_ptr1(uint64_t fn, uint64_t arg, uint32_t prior) {
  errno = prior;
  void *value = ((void *(*)(void *))(uintptr_t)fn)((void *)(uintptr_t)arg);
  int error = errno;
  return result(error, lean_box_uint64((uintptr_t)value));
}
LEAN_EXPORT lean_obj_res ls_logprim_void0(uint64_t fn) {
  ((void (*)(void))(uintptr_t)fn)();
  return lean_box(0);
}
LEAN_EXPORT lean_obj_res ls_logprim_void1(uint64_t fn, uint64_t arg) {
  ((void (*)(void *))(uintptr_t)fn)((void *)(uintptr_t)arg);
  return lean_box(0);
}
LEAN_EXPORT uint64_t ls_logprim_ulong0(uint64_t fn) {
  unsigned long value = ((unsigned long (*)(void))(uintptr_t)fn)();
  return (uint64_t)value;
}
LEAN_EXPORT lean_obj_res ls_logprim_int1(uint64_t fn, uint64_t arg, uint32_t prior) {
  errno = prior;
  int value = ((int (*)(void *))(uintptr_t)fn)((void *)(uintptr_t)arg);
  int error = errno;
  return result(error, lean_box_uint32((uint32_t)value));
}
LEAN_EXPORT uint64_t ls_logprim_long1(uint64_t fn, uint64_t arg) {
  long value = ((long (*)(void *))(uintptr_t)fn)((void *)(uintptr_t)arg);
  return (uint64_t)value;
}
LEAN_EXPORT lean_obj_res ls_logprim_int2(uint64_t fn, uint64_t arg, uint32_t value,
    uint32_t prior) {
  errno = prior;
  int rc = ((int (*)(void *, int))(uintptr_t)fn)((void *)(uintptr_t)arg, (int)value);
  int error = errno;
  return result(error, lean_box_uint32((uint32_t)rc));
}
LEAN_EXPORT lean_obj_res ls_logprim_ctrl(uint64_t fn, uint64_t arg, uint32_t command,
    uint64_t value, uint32_t prior) {
  errno = prior;
  long rc = ((long (*)(void *, int, long, void *))(uintptr_t)fn)(
      (void *)(uintptr_t)arg, (int)command, (long)value, NULL);
  int error = errno;
  return result(error, lean_box_uint64((uint64_t)rc));
}
LEAN_EXPORT lean_obj_res ls_logprim_verify(uint64_t fn, uint64_t ctx, uint32_t mode,
    uint32_t prior) {
  errno = prior;
  ((void (*)(void *, int, void *))(uintptr_t)fn)((void *)(uintptr_t)ctx, (int)mode, NULL);
  int error = errno;
  return result(error, lean_box(0));
}
LEAN_EXPORT lean_obj_res ls_logprim_ca(uint64_t fn, uint64_t ctx,
    b_lean_obj_arg path, uint32_t prior) {
  errno = prior;
  int rc = ((int (*)(void *, const char *, const char *))(uintptr_t)fn)(
      (void *)(uintptr_t)ctx, lean_string_cstr(path), NULL);
  int error = errno;
  return result(error, lean_box_uint32((uint32_t)rc));
}
LEAN_EXPORT lean_obj_res ls_logprim_cert(uint64_t fn, uint64_t ctx,
    b_lean_obj_arg path, uint32_t prior) {
  errno = prior;
  int rc = ((int (*)(void *, const char *))(uintptr_t)fn)(
      (void *)(uintptr_t)ctx, lean_string_cstr(path));
  int error = errno;
  return result(error, lean_box_uint32((uint32_t)rc));
}
LEAN_EXPORT lean_obj_res ls_logprim_key(uint64_t fn, uint64_t ctx,
    b_lean_obj_arg path, uint32_t prior) {
  errno = prior;
  int rc = ((int (*)(void *, const char *, int))(uintptr_t)fn)(
      (void *)(uintptr_t)ctx, lean_string_cstr(path), LS_SSL_FILETYPE_PEM);
  int error = errno;
  return result(error, lean_box_uint32((uint32_t)rc));
}
LEAN_EXPORT lean_obj_res ls_logprim_sni(uint64_t fn, uint64_t ssl,
    b_lean_obj_arg host, uint32_t prior) {
  errno = prior;
  long rc = ((long (*)(void *, int, long, void *))(uintptr_t)fn)(
      (void *)(uintptr_t)ssl, LS_SSL_CTRL_SET_TLSEXT_HOSTNAME,
      LS_TLSEXT_NAMETYPE_HOST_NAME, (void *)lean_string_cstr(host));
  int error = errno;
  return result(error, lean_box_uint64((uint64_t)rc));
}
LEAN_EXPORT lean_obj_res ls_logprim_tls_connect(uint64_t fn, uint64_t ssl) {
  errno = 0;
  int rc = ((int (*)(void *))(uintptr_t)fn)((void *)(uintptr_t)ssl);
  int error = errno;
  return result(error, lean_box_uint32((uint32_t)rc));
}
LEAN_EXPORT lean_obj_res ls_logprim_tls_send(uint64_t fn, uint64_t ssl,
    b_lean_obj_arg bytes, size_t offset, size_t count) {
  size_t size = lean_sarray_size(bytes);
  if (offset > size || count > size - offset || count > INT_MAX)
    return result(EINVAL, lean_box_uint32((uint32_t)-1));
  errno = 0;
  int rc = ((int (*)(void *, const void *, int))(uintptr_t)fn)(
      (void *)(uintptr_t)ssl, lean_sarray_cptr(bytes) + offset, (int)count);
  int error = errno;
  return result(error, lean_box_uint32((uint32_t)rc));
}
LEAN_EXPORT lean_obj_res ls_logprim_tls_recv(uint64_t fn, uint64_t ssl,
    lean_obj_arg bytes, size_t offset, size_t count) {
  size_t size = lean_sarray_size(bytes);
  if (offset > size || count > size - offset || count > INT_MAX)
    return result(EINVAL, pair(lean_box_uint32((uint32_t)-1), bytes));
  bytes = lean_sarray_ensure_exclusive(bytes);
  errno = 0;
  int rc = ((int (*)(void *, void *, int))(uintptr_t)fn)(
      (void *)(uintptr_t)ssl, lean_sarray_cptr(bytes) + offset, (int)count);
  int error = errno;
  return result(error, pair(lean_box_uint32((uint32_t)rc), bytes));
}
LEAN_EXPORT uint32_t ls_logprim_cert_host(uint64_t fn, uint64_t cert,
    b_lean_obj_arg host, size_t length, uint32_t flags) {
  int rc = ((int (*)(void *, const char *, size_t, unsigned, char **))(uintptr_t)fn)(
      (void *)(uintptr_t)cert, lean_string_cstr(host), length, flags, NULL);
  return (uint32_t)rc;
}
LEAN_EXPORT uint32_t ls_logprim_cert_ip(uint64_t fn, uint64_t cert, b_lean_obj_arg address) {
  int rc = ((int (*)(void *, const unsigned char *, size_t, unsigned))(uintptr_t)fn)(
      (void *)(uintptr_t)cert, lean_sarray_cptr(address), lean_sarray_size(address), 0);
  return (uint32_t)rc;
}
LEAN_EXPORT uint32_t ls_logprim_cert_ext(uint64_t fn, uint64_t cert) {
  int rc = ((int (*)(void *, int, int))(uintptr_t)fn)(
      (void *)(uintptr_t)cert, LS_NID_SUBJECT_ALT_NAME, -1);
  return (uint32_t)rc;
}
LEAN_EXPORT lean_obj_res ls_logprim_reason(uint64_t fn, uint64_t error) {
  const char *reason = ((const char *(*)(unsigned long))(uintptr_t)fn)((unsigned long)error);
  lean_object *value = lean_box(0);
  if (reason) {
    value = lean_alloc_ctor(1, 1, 0);
    lean_ctor_set(value, 0, lean_mk_string(reason));
  }
  return value;
}
