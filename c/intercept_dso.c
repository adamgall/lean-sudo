/* sudo 1.9.17p2 exec_intercept.c / intercept.proto transport.
 * Policy belongs exclusively to ls_intercept_check, never to this codec.
 * Despite intercept.proto's comment, sudo's framing is a HOST-order uint32_t.
 * Protobuf fixed64 values are little endian; the authentication token itself
 * is the raw native union of two uint64_t values, as in sudo_intercept_common.c.
 */
#include "intercept.h"
#include "intercept_dso.h"
#include <sys/socket.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <netinet/in.h>
#include <netinet/tcp.h>
#include <errno.h>
#include <fcntl.h>
#include <limits.h>
#include <poll.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#define DSO_PATH "/usr/libexec/sudo/sudo_intercept.so"
#define MESSAGE_MAX 2097152U
#define BOOTSTRAP_FD_MIN 64

enum phase { TOKEN, POLICY, HELLO, RESPONSE };
struct client {
    struct client *next;
    int fd;
    enum phase phase, after_response;
    unsigned char secret[16];
    size_t secret_used, header_used, used, length;
    uint32_t header;
    unsigned char *buffer;
    int close_after_response;
};
static int listener = -1, child_fd = -1, log_only;
static uint16_t listen_port;
static union { uint64_t words[2]; unsigned char bytes[16]; } token;
static struct client *clients;
static struct pollfd *pollfds;
static size_t poll_capacity;

static int set_flags(int fd, int nonblocking)
{
    int flags = fcntl(fd, F_GETFD);
    if (flags == -1 || fcntl(fd, F_SETFD, flags | FD_CLOEXEC) == -1)
        return -1;
    if (nonblocking) {
        flags = fcntl(fd, F_GETFL);
        if (flags == -1 || fcntl(fd, F_SETFL, flags | O_NONBLOCK) == -1)
            return -1;
    }
#ifdef SO_NOSIGPIPE
    int one = 1;
    if (setsockopt(fd, SOL_SOCKET, SO_NOSIGPIPE, &one, sizeof(one)) == -1)
        return -1;
#endif
    return 0;
}

static void destroy_client(struct client *c)
{
    close(c->fd);
    free(c->buffer);
    free(c);
}

void ls_intercept_dso_parent(void)
{
    if (child_fd != -1) close(child_fd);
    child_fd = -1;
}

void ls_intercept_dso_detach_service(void)
{
    if (listener != -1) close(listener);
    listener = -1;
    while (clients) {
        struct client *c = clients;
        clients = c->next;
        destroy_client(c);
    }
    free(pollfds);
    pollfds = NULL;
    poll_capacity = 0;
    memset(&token, 0, sizeof(token));
    listen_port = 0;
}

void ls_intercept_dso_close(void)
{
    ls_intercept_dso_parent();
    ls_intercept_dso_detach_service();
}

void ls_intercept_dso_set_log_only(int enabled) { log_only = enabled != 0; }

static int random_token(void)
{
    int fd = open("/dev/urandom", O_RDONLY | O_CLOEXEC);
    if (fd == -1) return -1;
    do {
        size_t done = 0;
        while (done != sizeof(token)) {
            ssize_t n = read(fd, token.bytes + done, sizeof(token) - done);
            if (n < 0 && errno == EINTR) continue;
            if (n <= 0) {
                int saved = n == 0 ? EIO : errno;
                close(fd);
                errno = saved;
                return -1;
            }
            done += (size_t)n;
        }
    } while (!(token.words[0] | token.words[1]));
    close(fd);
    return 0;
}

int ls_intercept_dso_prepare(void)
{
    struct stat sb;
    struct sockaddr_in addr;
    socklen_t addrlen = sizeof(addr);
    int pair[2] = { -1, -1 };
    struct client *initial = NULL;
    ls_intercept_dso_close();
    if (stat(DSO_PATH, &sb) == -1) return -1;
    if (!S_ISREG(sb.st_mode)) { errno = EINVAL; return -1; }
    if (random_token() == -1) goto bad;
    listener = socket(AF_INET, SOCK_STREAM, 0);
    if (listener == -1 || set_flags(listener, 1) == -1) goto bad;
    memset(&addr, 0, sizeof(addr));
    addr.sin_family = AF_INET;
    addr.sin_addr.s_addr = htonl(INADDR_LOOPBACK);
    if (bind(listener, (struct sockaddr *)&addr, sizeof(addr)) == -1 ||
        getsockname(listener, (struct sockaddr *)&addr, &addrlen) == -1 ||
        listen(listener, SOMAXCONN) == -1) goto bad;
    listen_port = ntohs(addr.sin_port);
    if (socketpair(AF_UNIX, SOCK_STREAM, 0, pair) == -1) goto bad;
    if (set_flags(pair[0], 1) == -1 || set_flags(pair[1], 0) == -1) goto bad;
    child_fd = fcntl(pair[1], F_DUPFD_CLOEXEC, BOOTSTRAP_FD_MIN);
    if (child_fd == -1) goto bad;
    close(pair[1]);
    pair[1] = -1;
    initial = calloc(1, sizeof(*initial));
    if (!initial) goto bad;
    initial->fd = pair[0];
    initial->phase = HELLO;
    clients = initial;
    return 0;
bad: {
    int saved = errno;
    if (pair[0] != -1) close(pair[0]);
    if (pair[1] != -1) close(pair[1]);
    ls_intercept_dso_close();
    errno = saved;
    return -1;
}}

int ls_intercept_dso_child(void)
{
    if (!ls_intercept_active() || ls_intercept_trace()) return 0;
    ls_intercept_dso_detach_service();
    if (child_fd == -1) { errno = EBADF; return -1; }
    int flags = fcntl(child_fd, F_GETFD);
    if (flags == -1) return -1;
    /* The sole intentional CLOEXEC exception: the DSO constructor consumes
     * and closes this socket during the initial executable's startup. */
    return fcntl(child_fd, F_SETFD, flags & ~FD_CLOEXEC);
}

char **ls_intercept_dso_environment(char *const envp[])
{
    size_t count = 0, preload_len = sizeof("LD_PRELOAD=" DSO_PATH);
    if (child_fd == -1) { errno = EBADF; return NULL; }
    for (; envp && envp[count]; count++) {
        if (strncmp(envp[count], "LD_PRELOAD=", 11) == 0) {
            size_t len = strlen(envp[count] + 11);
            if (len > SIZE_MAX - preload_len - 1) { errno = EOVERFLOW; return NULL; }
            preload_len += len + 1;
        }
    }
    if (count > SIZE_MAX / sizeof(char *) - 3) { errno = EOVERFLOW; return NULL; }
    char **out = calloc(count + 3, sizeof(*out));
    if (!out) return NULL;
    out[0] = malloc(preload_len);
    out[1] = malloc(sizeof("SUDO_INTERCEPT_FD=") + 3 * sizeof(int));
    if (!out[0] || !out[1]) {
        ls_intercept_dso_free_environment(out);
        return NULL;
    }
    char *end = stpcpy(out[0], "LD_PRELOAD=" DSO_PATH);
    size_t dest = 2;
    for (size_t i = 0; i < count; i++) {
        if (strncmp(envp[i], "LD_PRELOAD=", 11) == 0) {
            if (envp[i][11]) {
                *end++ = ':';
                end = stpcpy(end, envp[i] + 11);
            }
        } else if (strncmp(envp[i], "SUDO_INTERCEPT_FD=", 18) != 0) {
            out[dest++] = envp[i];
        }
    }
    snprintf(out[1], sizeof("SUDO_INTERCEPT_FD=") + 3 * sizeof(int),
        "SUDO_INTERCEPT_FD=%d", child_fd);
    return out;
}

void ls_intercept_dso_free_environment(char **envp)
{
    if (envp) { free(envp[0]); free(envp[1]); free(envp); }
}

/* Strict schema-specific protobuf decoding: no truncated/overflowing varints,
 * unsupported wire types, duplicate singular fields or embedded NUL strings. */
struct cursor { const unsigned char *p, *end; };
static int varint(struct cursor *in, uint64_t *value)
{
    uint64_t v = 0;
    for (unsigned int shift = 0; shift < 70; shift += 7) {
        if (in->p == in->end) return -1;
        unsigned int byte = *in->p++;
        if (shift == 63 && byte > 1) return -1;
        v |= (uint64_t)(byte & 127) << shift;
        if (!(byte & 128)) { *value = v; return 0; }
    }
    return -1;
}

static int bytes(struct cursor *in, struct cursor *value)
{
    uint64_t len;
    if (varint(in, &len) == -1 || len > (uint64_t)(in->end - in->p)) return -1;
    value->p = in->p;
    value->end = in->p + (size_t)len;
    in->p = value->end;
    return 0;
}

struct request {
    char *command, *cwd, **argv, **envp;
    void *allocation;
};

static int parse_policy(struct cursor body, struct request *req)
{
    size_t argc = 0, envc = 0, string_bytes = 0;
    unsigned int seen = 0;
    struct cursor scan = body, value;
    uint64_t key, integer;
    while (scan.p != scan.end) {
        if (varint(&scan, &key) == -1) return -1;
        if (key == 40) {
            if ((seen & 32) || varint(&scan, &integer) == -1 || integer > INT_MAX) return -1;
            seen |= 32;
            continue;
        }
        if (key != 10 && key != 18 && key != 26 && key != 34) return -1;
        if (bytes(&scan, &value) == -1 || memchr(value.p, 0, (size_t)(value.end - value.p))) return -1;
        if (key == 10 || key == 18) {
            unsigned int bit = 1U << (key >> 3);
            if (seen & bit) return -1;
            seen |= bit;
        } else if (key == 26) argc++;
        else envc++;
        string_bytes += (size_t)(value.end - value.p) + 1;
    }
    if (!(seen & 2)) return -1;
    size_t argv_slots = argc ? argc : 1;
    size_t pointer_bytes = (argv_slots + envc + 2) * sizeof(char *);
    req->allocation = calloc(1, pointer_bytes + string_bytes);
    if (!req->allocation) return -1;
    req->argv = req->allocation;
    req->envp = req->argv + argv_slots + 1;
    char *text = (char *)req->allocation + pointer_bytes;
    argc = envc = 0;
    while (body.p != body.end) {
        if (varint(&body, &key) == -1) goto bad;
        if (key == 40) {
            if (varint(&body, &integer) == -1) goto bad;
            continue;
        }
        if (bytes(&body, &value) == -1) goto bad;
        size_t len = (size_t)(value.end - value.p);
        memcpy(text, value.p, len);
        text[len] = 0;
        switch (key) {
        case 10: req->command = text; break;
        case 18: req->cwd = text; break;
        case 26: req->argv[argc++] = text; break;
        case 34: req->envp[envc++] = text; break;
        }
        text += len + 1;
    }
    if (!req->command[0]) goto bad;
    /* sudo's plugin API replaces argv[0] with the requested command. */
    req->argv[0] = req->command;
    return 0;
bad:
    free(req->allocation);
    req->allocation = NULL;
    return -1;
}

static size_t varint_size(uint64_t n)
{
    size_t size = 1;
    while (n >= 128) { n >>= 7; size++; }
    return size;
}
static unsigned char *put_varint(unsigned char *p, uint64_t n)
{
    while (n >= 128) { *p++ = (unsigned char)(n | 128); n >>= 7; }
    *p++ = (unsigned char)n;
    return p;
}
static size_t string_size(const char *s)
{
    size_t len = strlen(s);
    return 1 + varint_size(len) + len;
}
static unsigned char *put_string(unsigned char *p, unsigned int field, const char *s)
{
    size_t len = strlen(s);
    *p++ = (unsigned char)((field << 3) | 2);
    p = put_varint(p, len);
    memcpy(p, s, len);
    return p + len;
}
static unsigned char *response(struct client *c, unsigned int field, size_t body_len)
{
    size_t wire_len = 1 + varint_size(body_len) + body_len;
    if (wire_len > MESSAGE_MAX) { errno = EMSGSIZE; return NULL; }
    unsigned char *buf = malloc(sizeof(uint32_t) + wire_len);
    if (!buf) return NULL;
    free(c->buffer);
    c->buffer = buf;
    c->used = 0;
    c->length = sizeof(uint32_t) + wire_len;
    uint32_t header = (uint32_t)wire_len;
    memcpy(buf, &header, sizeof(header));
    buf += sizeof(header);
    *buf++ = (unsigned char)((field << 3) | 2);
    c->phase = RESPONSE;
    return put_varint(buf, body_len);
}

static int hello_response(struct client *c)
{
    unsigned char *p = response(c, 1, 18 + 1 + varint_size(listen_port) + 2);
    if (!p) return -1;
    for (unsigned int word = 0; word < 2; word++) {
        *p++ = (unsigned char)(((word + 1) << 3) | 1);
        for (unsigned int byte = 0; byte < 8; byte++)
            *p++ = (unsigned char)(token.words[word] >> (8 * byte));
    }
    *p++ = 24;
    p = put_varint(p, listen_port);
    *p++ = 32;
    *p = (unsigned char)log_only;
    c->close_after_response = 1;
    return 0;
}

static int policy_response(struct client *c, struct request *req, int result)
{
    if (result != 1) {
        const char *message = result == 0 ? "command rejected by policy" : "intercept policy error";
        unsigned char *p = response(c, result == 0 ? 3 : 4, string_size(message));
        if (!p) return -1;
        put_string(p, 1, message);
        c->close_after_response = 1;
        return 0;
    }
    size_t size = string_size(req->command);
    for (size_t i = 0; req->argv[i]; i++) size += string_size(req->argv[i]);
    for (size_t i = 0; req->envp[i]; i++) size += string_size(req->envp[i]);
    unsigned char *p = response(c, 2, size);
    if (!p) return -1;
    p = put_string(p, 1, req->command);
    for (size_t i = 0; req->argv[i]; i++) p = put_string(p, 2, req->argv[i]);
    for (size_t i = 0; req->envp[i]; i++) p = put_string(p, 3, req->envp[i]);
    c->after_response = HELLO;
    return 0;
}

static int check_request(struct request *req)
{
    struct stat sb;
    int dirfd = AT_FDCWD, rc;
    if (req->command[0] != '/') {
        if (!req->cwd || !req->cwd[0]) return -1;
        dirfd = open(req->cwd, O_RDONLY | O_DIRECTORY | O_CLOEXEC);
        if (dirfd == -1) return -1;
    }
    rc = fstatat(dirfd, req->command, &sb, 0);
    int saved = errno;
    if (dirfd != AT_FDCWD) close(dirfd);
    errno = saved;
    if (rc == -1) return -1;
    /* No pid exists in PolicyCheckRequest. Do not misattribute forked execs
     * using the pid from the initial constructor's Hello. */
    return ls_intercept_check(req->command, req->argv, req->envp,
        req->cwd ? req->cwd : "", 0, (sb.st_mode & (S_ISUID | S_ISGID)) != 0);
}

static int dispatch(struct client *c)
{
    struct cursor wire = { c->buffer, c->buffer + c->length }, body;
    uint64_t key, pid;
    if (varint(&wire, &key) == -1 || bytes(&wire, &body) == -1 || wire.p != wire.end) return -1;
    if (c->phase == HELLO) {
        if (key != 18 || varint(&body, &key) == -1 || key != 8 ||
            varint(&body, &pid) == -1 || pid == 0 || pid > INT_MAX || body.p != body.end) return -1;
        return hello_response(c);
    }
    if (c->phase != POLICY || key != 10) return -1;
    struct request req = { 0 };
    if (parse_policy(body, &req) == -1) return -1;
    int result = check_request(&req);
    int rc;
    if (log_only) {
        /* The upstream client does not wait for a policy response in this
         * mode. Only a subsequent constructor Hello receives a response. */
        rc = result == 1 ? 0 : -1;
        free(c->buffer);
        c->buffer = NULL;
        c->length = c->used = c->header_used = 0;
        c->phase = HELLO;
    } else {
        rc = policy_response(c, &req, result);
    }
    free(req.allocation);
    return rc;
}

/* Return 1 complete, 0 would-block, -1 EOF/error. */
static int receive(int fd, void *buffer, size_t *used, size_t length)
{
    while (*used < length) {
        ssize_t n = recv(fd, (unsigned char *)buffer + *used, length - *used, 0);
        if (n > 0) { *used += (size_t)n; continue; }
        if (n == -1 && errno == EINTR) continue;
        if (n == -1 && (errno == EAGAIN || errno == EWOULDBLOCK)) return 0;
        return -1;
    }
    return 1;
}

static int read_client(struct client *c)
{
    int rc;
    if (c->phase == TOKEN) {
        rc = receive(c->fd, c->secret, &c->secret_used, sizeof(c->secret));
        if (rc <= 0) return rc;
        unsigned int difference = 0;
        for (size_t i = 0; i < sizeof(token); i++) difference |= c->secret[i] ^ token.bytes[i];
        if (difference) return -1;
        c->phase = POLICY;
    }
    rc = receive(c->fd, &c->header, &c->header_used, sizeof(c->header));
    if (rc <= 0) return rc;
    if (!c->buffer) {
        if (!c->header || c->header > MESSAGE_MAX) return -1;
        c->length = c->header;
        c->buffer = malloc(c->length);
        if (!c->buffer) return -1;
    }
    rc = receive(c->fd, c->buffer, &c->used, c->length);
    if (rc <= 0) return rc;
    return dispatch(c);
}

static int write_client(struct client *c)
{
    while (c->used < c->length) {
        int flags = 0;
#ifdef MSG_NOSIGNAL
        flags = MSG_NOSIGNAL;
#endif
        ssize_t n = send(c->fd, c->buffer + c->used, c->length - c->used, flags);
        if (n > 0) { c->used += (size_t)n; continue; }
        if (n == -1 && errno == EINTR) continue;
        if (n == -1 && (errno == EAGAIN || errno == EWOULDBLOCK)) return 0;
        return -1;
    }
    if (c->close_after_response) return -1;
    free(c->buffer);
    c->buffer = NULL;
    c->header_used = c->used = c->length = 0;
    c->phase = c->after_response;
    return 0;
}

static void accept_client(void)
{
    struct sockaddr_in addr;
    socklen_t len = sizeof(addr);
    int fd = accept(listener, (struct sockaddr *)&addr, &len);
    if (fd == -1) return;
    if (addr.sin_family != AF_INET || addr.sin_addr.s_addr != htonl(INADDR_LOOPBACK) ||
        set_flags(fd, 1) == -1) { close(fd); return; }
    int one = 1;
    if (setsockopt(fd, IPPROTO_TCP, TCP_NODELAY, &one, sizeof(one)) == -1) { close(fd); return; }
    struct client *c = calloc(1, sizeof(*c));
    if (!c) { close(fd); return; }
    c->fd = fd;
    c->phase = TOKEN;
    c->next = clients;
    clients = c;
}

int ls_intercept_dso_service(int timeout_ms)
{
    if (listener == -1) { errno = EBADF; return -1; }
    size_t count = 1;
    for (struct client *c = clients; c; c = c->next) count++;
    if (count > poll_capacity) {
        if (count > SIZE_MAX / sizeof(*pollfds)) { errno = EOVERFLOW; return -1; }
        struct pollfd *newfds = realloc(pollfds, count * sizeof(*pollfds));
        if (!newfds) return -1;
        pollfds = newfds;
        poll_capacity = count;
    }
    pollfds[0] = (struct pollfd){ .fd = listener, .events = POLLIN };
    size_t index = 1;
    for (struct client *c = clients; c; c = c->next)
        pollfds[index++] = (struct pollfd){ .fd = c->fd,
            .events = c->phase == RESPONSE ? POLLOUT : POLLIN };
    int rc = poll(pollfds, (nfds_t)count, timeout_ms);
    if (rc == -1) return errno == EINTR ? 0 : -1;
    if (!rc) return 0;
    index = 1;
    struct client **link = &clients;
    while (*link) {
        struct client *c = *link;
        short events = pollfds[index++].revents;
        int failed = (events & (POLLERR | POLLNVAL)) != 0;
        if (!failed && (events & (POLLIN | POLLOUT | POLLHUP)))
            failed = (c->phase == RESPONSE ? write_client(c) : read_client(c)) == -1;
        if (failed) {
            *link = c->next;
            destroy_client(c);
        } else link = &c->next;
    }
    if (pollfds[0].revents & (POLLERR | POLLHUP | POLLNVAL)) { errno = EIO; return -1; }
    if (pollfds[0].revents & POLLIN) accept_client();
    return 0;
}
