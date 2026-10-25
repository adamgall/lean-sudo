/* Privileged interception broker. This file transports facts; Lean alone
 * authorizes them. Each request has its own reply socket, so forked tracees
 * cannot consume another process's authorization. */
#include <lean/lean.h>
#include "intercept.h"
#include "intercept_dso.h"
#include "logsrv.h"
#include <errno.h>
#include <fcntl.h>
#include <poll.h>
#include <signal.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <sys/socket.h>
#include <sys/wait.h>
#include <unistd.h>

#define REQUEST_MAX (4U * 1024U * 1024U)
static int broker_fd = -1, active, tracing, verifying;
static pid_t broker_pid = -1;
static lean_object *policy_callback;

int ls_intercept_active(void) { return active; }
int ls_intercept_trace(void) { return active && tracing; }
int ls_intercept_verify(void) { return active && verifying; }

static int utf8_valid(const char *str, size_t n) {
  const unsigned char *s = (const unsigned char *)str;
  size_t i = 0;
  while (i < n) {
    unsigned c = s[i], lo = 0x80, hi = 0xbf;
    size_t need;
    if (c < 0x80) { i++; continue; }
    else if (c >= 0xc2 && c <= 0xdf) need = 1;
    else if (c == 0xe0) { need = 2; lo = 0xa0; }
    else if ((c >= 0xe1 && c <= 0xec) || c == 0xee || c == 0xef) need = 2;
    else if (c == 0xed) { need = 2; hi = 0x9f; }
    else if (c == 0xf0) { need = 3; lo = 0x90; }
    else if (c >= 0xf1 && c <= 0xf3) need = 3;
    else if (c == 0xf4) { need = 3; hi = 0x8f; }
    else return 0;
    if (n - i - 1 < need || s[i + 1] < lo || s[i + 1] > hi) return 0;
    for (size_t k = 2; k <= need; k++) if ((s[i + k] & 0xc0) != 0x80) return 0;
    i += need + 1;
  }
  return 1;
}

static int transfer(int fd, void *buf, size_t len, int sending) {
  unsigned char *p = buf;
  while (len) {
    ssize_t n = sending ? send(fd, p, len, MSG_NOSIGNAL) : read(fd, p, len);
    if (n < 0 && errno == EINTR) continue;
    if (n <= 0) return -1;
    p += n; len -= (size_t)n;
  }
  return 0;
}
static int send_string(int fd, const char *s, size_t *total) {
  size_t n = strlen(s);
  if (n > REQUEST_MAX || *total > REQUEST_MAX - n) return -1;
  *total += n;
  uint32_t len = (uint32_t)n;
  return transfer(fd, &len, sizeof len, 1) || transfer(fd, (void *)s, n, 1) ? -1 : 0;
}
static int send_array(int fd, char *const a[], size_t *total) {
  uint32_t n = 0;
  if (a) while (a[n]) { if (++n > REQUEST_MAX / 4) return -1; }
  if (transfer(fd, &n, sizeof n, 1)) return -1;
  for (uint32_t i = 0; i < n; i++) if (send_string(fd, a[i], total)) return -1;
  return 0;
}
static lean_object *receive_string(int fd, size_t *total) {
  uint32_t n;
  if (transfer(fd, &n, sizeof n, 0) || n > REQUEST_MAX || *total > REQUEST_MAX - n)
    return NULL;
  *total += n;
  char *s = malloc((size_t)n + 1);
  if (!s) return NULL;
  if (transfer(fd, s, n, 0) || memchr(s, 0, n) || !utf8_valid(s, n)) {
    free(s); return NULL;
  }
  s[n] = 0;
  lean_object *r = lean_mk_string_from_bytes_unchecked(s, n);
  free(s);
  return r;
}
static lean_object *receive_array(int fd, size_t *total) {
  uint32_t n;
  if (transfer(fd, &n, sizeof n, 0) || n > REQUEST_MAX / 4) return NULL;
  lean_object *a = lean_mk_empty_array_with_capacity(lean_box(n));
  for (uint32_t i = 0; i < n; i++) {
    lean_object *s = receive_string(fd, total);
    if (!s) { lean_dec(a); return NULL; }
    a = lean_array_push(a, s);
  }
  return a;
}
static int call_policy(lean_object *command, lean_object *cwd, lean_object *argv,
    lean_object *env, uint32_t pid, uint8_t setid) {
  lean_object *req = lean_alloc_ctor(0, 4, 5);
  lean_ctor_set(req, 0, command); lean_ctor_set(req, 1, cwd);
  lean_ctor_set(req, 2, argv); lean_ctor_set(req, 3, env);
  lean_ctor_set_uint32(req, 4 * sizeof(void *), pid);
  lean_ctor_set_uint8(req, 4 * sizeof(void *) + 4, setid != 0);
  lean_inc(policy_callback);
  lean_object *result = lean_apply_2(policy_callback, req, lean_io_mk_world());
  int allow = lean_io_result_is_ok(result) && lean_unbox(lean_io_result_get_value(result)) == 1;
  lean_dec(result);
  return allow;
}
static lean_object *string_array(char *const words[]) {
  lean_object *a = lean_mk_empty_array_with_capacity(lean_box(0));
  if (words) for (size_t i = 0; words[i]; i++) {
    if (!utf8_valid(words[i], strlen(words[i]))) { lean_dec(a); return NULL; }
    a = lean_array_push(a, lean_mk_string(words[i]));
  }
  return a;
}
int ls_intercept_check(const char *command, char *const argv[], char *const envp[],
    const char *cwd, pid_t pid, int setid) {
  if (!active || !command || !cwd) { errno = EACCES; return -1; }
  if (policy_callback) {
    if (!utf8_valid(command, strlen(command)) || !utf8_valid(cwd, strlen(cwd))) return -1;
    lean_object *args = string_array(argv), *env = string_array(envp);
    if (!args || !env) {
      if (args) lean_dec(args);
      if (env) lean_dec(env);
      return -1;
    }
    return call_policy(lean_mk_string(command), lean_mk_string(cwd), args, env,
      (uint32_t)pid, setid != 0);
  }
  int pair[2];
  if (broker_fd < 0 || socketpair(AF_UNIX, SOCK_STREAM | SOCK_CLOEXEC, 0, pair)) return -1;
  char byte = 'R';
  struct iovec iov = { &byte, 1 };
  union { struct cmsghdr align; char bytes[CMSG_SPACE(sizeof(int))]; } control;
  memset(&control, 0, sizeof control);
  struct msghdr msg = { .msg_iov = &iov, .msg_iovlen = 1,
    .msg_control = control.bytes, .msg_controllen = sizeof control.bytes };
  struct cmsghdr *c = CMSG_FIRSTHDR(&msg);
  c->cmsg_level = SOL_SOCKET; c->cmsg_type = SCM_RIGHTS; c->cmsg_len = CMSG_LEN(sizeof(int));
  memcpy(CMSG_DATA(c), &pair[1], sizeof(int));
  int ok = sendmsg(broker_fd, &msg, MSG_NOSIGNAL) == 1;
  close(pair[1]);
  size_t total = 0;
  uint32_t facts[2] = { (uint32_t)pid, setid != 0 };
  uint8_t answer = 0;
  if (ok && !transfer(pair[0], facts, sizeof facts, 1) &&
      !send_string(pair[0], command, &total) && !send_string(pair[0], cwd, &total) &&
      !send_array(pair[0], argv, &total) && !send_array(pair[0], envp, &total)) {
    shutdown(pair[0], SHUT_WR);
    for (;;) {
      struct pollfd p[2] = {{ .fd = pair[0], .events = POLLIN },
        { .fd = ls_logsrv_queue_fd(), .events = POLLIN }};
      int ready = poll(p, 2, -1);
      if (ready < 0 && errno == EINTR) continue;
      if (ready < 0 || (p[1].revents && ls_logsrv_dispatch() != 0)) { ok = 0; break; }
      if (p[0].revents) { ok = !transfer(pair[0], &answer, sizeof answer, 0); break; }
    }
  } else ok = 0;
  close(pair[0]);
  if (!ok || answer > 1) { errno = EACCES; return -1; }
  return answer;
}
static void handle_request(int fd) {
  uint32_t facts[2]; size_t total = 0;
  lean_object *values[4] = { NULL, NULL, NULL, NULL };
  uint8_t answer = 0;
  if (transfer(fd, facts, sizeof facts, 0) || facts[1] > 1) goto done;
  values[0] = receive_string(fd, &total); if (!values[0]) goto done;
  values[1] = receive_string(fd, &total); if (!values[1]) goto done;
  values[2] = receive_array(fd, &total); if (!values[2]) goto done;
  values[3] = receive_array(fd, &total); if (!values[3]) goto done;
  char extra;
  if (read(fd, &extra, 1) != 0) goto done;
  answer = (uint8_t)call_policy(values[0], values[1], values[2], values[3], facts[0], (uint8_t)facts[1]);
  memset(values, 0, sizeof values);
done:
  for (unsigned i = 0; i < 4; i++) if (values[i]) lean_dec(values[i]);
  (void)transfer(fd, &answer, sizeof answer, 1);
  close(fd);
}
static void broker_loop(int fd) {
  for (;;) {
    if (!tracing && ls_intercept_dso_service(0) != 0) break;
    struct pollfd p = { .fd = fd, .events = POLLIN };
    int ready = poll(&p, 1, tracing ? -1 : 20);
    if (ready < 0 && errno == EINTR) continue;
    if (ready < 0) break;
    if (!ready) continue;
    char byte = 0;
    struct iovec iov = { &byte, 1 };
    union { struct cmsghdr align; char bytes[CMSG_SPACE(sizeof(int))]; } control;
    struct msghdr msg = { .msg_iov = &iov, .msg_iovlen = 1,
      .msg_control = control.bytes, .msg_controllen = sizeof control.bytes };
    ssize_t n = recvmsg(fd, &msg, MSG_CMSG_CLOEXEC);
    if (n < 0 && errno == EINTR) continue;
    if (n <= 0 || byte == 'Q') break;
    struct cmsghdr *c = CMSG_FIRSTHDR(&msg);
    if (n != 1 || byte != 'R' || (msg.msg_flags & (MSG_TRUNC | MSG_CTRUNC)) ||
        !c || c->cmsg_level != SOL_SOCKET || c->cmsg_type != SCM_RIGHTS ||
        c->cmsg_len != CMSG_LEN(sizeof(int))) continue;
    int request; memcpy(&request, CMSG_DATA(c), sizeof request);
    handle_request(request);
  }
  _exit(0);
}
lean_obj_res lean_sudo_intercept_start(uint8_t trace, uint8_t verify, uint8_t log_only,
    lean_obj_arg callback) {
  if (active) { lean_dec(callback); return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string("interception already active"))); }
  int pair[2];
  if (socketpair(AF_UNIX, SOCK_SEQPACKET | SOCK_CLOEXEC, 0, pair)) goto failed;
  tracing = trace != 0 && ls_intercept_trace_supported();
  verifying = verify != 0 && tracing;
  active = 1;
  if (!tracing) {
    ls_intercept_dso_set_log_only(log_only);
    if (ls_intercept_dso_prepare()) { close(pair[0]); close(pair[1]); goto failed; }
  }
  broker_pid = fork();
  if (broker_pid == 0) {
    close(pair[0]); policy_callback = callback;
    ls_logsrv_detach_child();
    if (!tracing) ls_intercept_dso_parent();
    broker_loop(pair[1]);
  }
  close(pair[1]);
  if (broker_pid < 0) { close(pair[0]); ls_intercept_dso_close(); goto failed; }
  broker_fd = pair[0];
  if (!tracing) ls_intercept_dso_detach_service();
  lean_dec(callback);
  return lean_io_result_mk_ok(lean_box(0));
failed:
  active = 0; lean_dec(callback);
  return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string("unable to initialize command interception")));
}
lean_obj_res lean_sudo_intercept_stop(void) {
  if (broker_fd >= 0) {
    char quit = 'Q';
    (void)send(broker_fd, &quit, 1, MSG_NOSIGNAL);
    close(broker_fd); broker_fd = -1;
  }
  ls_intercept_dso_close();
  if (broker_pid > 0) {
    int status;
    while (waitpid(broker_pid, &status, 0) < 0 && errno == EINTR) {}
    broker_pid = -1;
  }
  active = 0;
  return lean_io_result_mk_ok(lean_box(0));
}
