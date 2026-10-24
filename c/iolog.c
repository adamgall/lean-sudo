/* sudo-compatible on-disk I/O logs. Policy and metadata rendering live in Lean. */
#include <lean/lean.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <sys/ioctl.h>
#include <fcntl.h>
#include <unistd.h>
#include <pwd.h>
#include <grp.h>
#include <time.h>
#include <errno.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <limits.h>
#include <dlfcn.h>
#include <regex.h>
#include <signal.h>

static struct {
  int active, compressed, flush, ignore, passwords, filtered;
  uid_t uid;
  gid_t gid;
  mode_t mode;
  int fd[6];
  void *gz[6];
  regex_t *patterns;
  size_t npatterns;
  struct timespec last;
} logstate = {.fd = {-1, -1, -1, -1, -1, -1}};
static void *zlib;
static void *(*z_gzdopen)(int, const char *);
static int (*z_gzwrite)(void *, const void *, unsigned);
static int (*z_gzflush)(void *, int);
static int (*z_gzclose)(void *);

static lean_obj_res failure(const char *what) {
  char msg[512];
  snprintf(msg, sizeof msg, "%s: %s", what, strerror(errno));
  return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(msg)));
}
static int write_all(int fd, const void *v, size_t len) {
  const char *p = v;
  while (len) {
    ssize_t n = write(fd, p, len);
    if (n < 0 && errno == EINTR) continue;
    if (n <= 0) { if (!n) errno = EIO; return -1; }
    p += n; len -= (size_t)n;
  }
  return 0;
}
/* Walk from / with openat/O_NOFOLLOW. Never follow a log-path symlink, including
 * intermediate components, and never change permissions of existing ancestors. */
static int directory(const char *path) {
  if (*path != '/') { errno = EINVAL; return -1; }
  char *copy = strdup(path);
  if (!copy) return -1;
  int fd = open("/", O_RDONLY | O_DIRECTORY | O_CLOEXEC);
  char *save = NULL;
  mode_t mode = logstate.mode | 0700;
  if (mode & 0060) mode |= 0010;
  if (mode & 0006) mode |= 0001;
  for (char *p = strtok_r(copy, "/", &save); fd >= 0 && p; p = strtok_r(NULL, "/", &save)) {
    if (!strcmp(p, ".") || !strcmp(p, "..")) { close(fd); fd = -1; errno = EINVAL; break; }
    int made = mkdirat(fd, p, 0700) == 0;
    if (!made && errno != EEXIST) { close(fd); fd = -1; break; }
    int next = openat(fd, p, O_RDONLY | O_DIRECTORY | O_NOFOLLOW | O_CLOEXEC);
    int err = errno;
    close(fd); fd = next; errno = err;
    if (fd >= 0 && made && (fchown(fd, logstate.uid, logstate.gid) || fchmod(fd, mode))) {
      err = errno; close(fd); fd = -1; errno = err;
    }
  }
  /* As sudo does, enforce the configured owner/mode on the final directory,
   * including a reused session after sequence rollover, not its ancestors. */
  if (fd >= 0 && (fchown(fd, logstate.uid, logstate.gid) || fchmod(fd, mode))) {
    int err = errno; close(fd); fd = -1; errno = err;
  }
  int err = errno; free(copy); errno = err;
  return fd;
}
static int log_file(int dir, const char *name) {
  int fd = openat(dir, name, O_WRONLY | O_CREAT | O_NOFOLLOW | O_CLOEXEC | O_NONBLOCK, 0600);
  if (fd < 0) return -1;
  struct stat st;
  if (fstat(fd, &st) || !S_ISREG(st.st_mode) || st.st_nlink != 1 ||
      (st.st_uid != 0 && st.st_uid != logstate.uid) ||
      fchown(fd, logstate.uid, logstate.gid) || fchmod(fd, logstate.mode) || ftruncate(fd, 0)) {
    int err = errno ? errno : EINVAL; close(fd); errno = err; return -1;
  }
  return fd;
}
static void reset(void) {
  for (int i = 0; i < 6; i++) {
    if (logstate.gz[i]) { z_gzclose(logstate.gz[i]); logstate.gz[i] = NULL; }
    else if (logstate.fd[i] >= 0) close(logstate.fd[i]);
    logstate.fd[i] = -1;
  }
  for (size_t i = 0; i < logstate.npatterns; i++) regfree(&logstate.patterns[i]);
  free(logstate.patterns); logstate.patterns = NULL; logstate.npatterns = 0;
  logstate.active = 0;
}
/* Called in the forked command; do not flush the parent's copied gzip buffers. */
void ls_iolog_child_close(void) {
  if (!logstate.active) return;
  for (int i = 0; i < 6; i++) if (logstate.fd[i] >= 0) close(logstate.fd[i]);
  logstate.active = 0;
}
int ls_iolog_active(void) { return logstate.active; }
int ls_iolog_stream(int stream) { return logstate.active && stream >= 0 && stream < 5 && logstate.fd[stream] >= 0; }
static int failed(void) {
  int err = errno ? errno : EIO;
  int ignore = logstate.ignore;
  reset(); errno = err;
  return ignore ? 0 : -1;
}
static int put(int stream, const void *buf, size_t len) {
  if (logstate.compressed) {
    if (len > INT_MAX || z_gzwrite(logstate.gz[stream], buf, (unsigned)len) != (int)len) { errno = EIO; return -1; }
    if (logstate.flush && z_gzflush(logstate.gz[stream], 2) != 0) { errno = EIO; return -1; }
    return 0;
  }
  return write_all(logstate.fd[stream], buf, len);
}
static int timing(int event, const char *detail) {
  struct timespec now;
  if (clock_gettime(CLOCK_MONOTONIC, &now)) return -1;
  time_t sec = now.tv_sec - logstate.last.tv_sec;
  long ns = now.tv_nsec - logstate.last.tv_nsec;
  if (ns < 0) { sec--; ns += 1000000000; }
  if (sec < 0) { sec = 0; ns = 0; }
  char line[160];
  int n = snprintf(line, sizeof line, "%d %lld.%09ld %s\n", event, (long long)sec, ns, detail);
  if (n < 0 || (size_t)n >= sizeof line) { errno = EOVERFLOW; return -1; }
  if (put(5, line, (size_t)n)) return -1;
  logstate.last = now;
  return 0;
}
int ls_iolog_write(int stream, const void *buf, size_t len) {
  if (!logstate.active || stream < 0 || stream > 4) return 0;
  char *copy = NULL;
  if (!logstate.passwords && stream == 4) {
    copy = malloc(len + 1);
    if (!copy) return failed();
    memcpy(copy, buf, len); copy[len] = 0;
    logstate.filtered = 0;
    for (size_t i = 0; i < logstate.npatterns; i++)
      if (!regexec(&logstate.patterns[i], copy, 0, NULL, 0)) { logstate.filtered = 1; break; }
    free(copy); copy = NULL;
  }
  if (logstate.fd[stream] < 0 || !len) return 0;
  if (!logstate.passwords && stream == 3 && logstate.filtered) {
    copy = malloc(len);
    if (!copy) return failed();
    memcpy(copy, buf, len);
    for (size_t i = 0; i < len; i++) {
      if (copy[i] == '\n' || copy[i] == '\r') { logstate.filtered = 0; break; }
      copy[i] = '*';
    }
    buf = copy;
  }
  int rc = put(stream, buf, len);
  free(copy);
  char detail[32]; snprintf(detail, sizeof detail, "%zu", len);
  if (rc || timing(stream, detail)) return failed();
  return 0;
}
int ls_iolog_winsize(unsigned rows, unsigned cols) {
  if (!logstate.active) return 0;
  char detail[64]; snprintf(detail, sizeof detail, "%u %u", rows, cols);
  return timing(5, detail) ? failed() : 0;
}
int ls_iolog_suspend(int sig) {
  if (!logstate.active) return 0;
  const char *name = sig == SIGCONT ? "CONT" : sig == SIGTSTP ? "TSTP" :
    sig == SIGTTIN ? "TTIN" : sig == SIGTTOU ? "TTOU" : "STOP";
  return timing(7, name) ? failed() : 0;
}
int ls_iolog_close(int exit_code, int signal_number) {
  (void)exit_code; (void)signal_number;
  if (!logstate.active) return 0;
  int rc = 0, ignore = logstate.ignore;
  /* sudoreplay uses cleared timing write bits to distinguish completed logs. */
  if (logstate.fd[5] >= 0 && fchmod(logstate.fd[5], logstate.mode & ~0222)) rc = -1;
  for (int i = 0; i < 6; i++) {
    if (logstate.gz[i]) { if (z_gzclose(logstate.gz[i])) rc = -1; logstate.gz[i] = NULL; }
    else if (logstate.fd[i] >= 0 && close(logstate.fd[i])) rc = -1;
    logstate.fd[i] = -1;
  }
  reset();
  if (rc) errno = EIO;
  return ignore ? 0 : rc;
}
LEAN_EXPORT lean_obj_res leansudo_iolog_abort(lean_obj_arg world) {
  (void)world; reset(); return lean_io_result_mk_ok(lean_box(0));
}
LEAN_EXPORT lean_obj_res leansudo_iolog_clock(b_lean_obj_arg formats, lean_obj_arg world) {
  (void)world;
  struct timespec now;
  struct tm tm;
  if (clock_gettime(CLOCK_REALTIME, &now) || !localtime_r(&now.tv_sec, &tm)) return failure("I/O log clock");
  size_t count = lean_array_size(formats);
  lean_object *a = lean_mk_empty_array_with_capacity(lean_unsigned_to_nat(count + 4));
  char buf[256]; snprintf(buf, sizeof buf, "%lld", (long long)now.tv_sec);
  a = lean_array_push(a, lean_mk_string(buf));
  snprintf(buf, sizeof buf, "%ld", now.tv_nsec); a = lean_array_push(a, lean_mk_string(buf));
  struct winsize ws = {0};
  int ttyfd = open("/dev/tty", O_RDONLY | O_NOCTTY | O_CLOEXEC);
  if (ttyfd >= 0) { if (ioctl(ttyfd, TIOCGWINSZ, &ws)) memset(&ws, 0, sizeof ws); close(ttyfd); }
  snprintf(buf, sizeof buf, "%u", ws.ws_row); a = lean_array_push(a, lean_mk_string(buf));
  snprintf(buf, sizeof buf, "%u", ws.ws_col); a = lean_array_push(a, lean_mk_string(buf));
  for (size_t i = 0; i < count; i++) {
    char format[4];
    snprintf(format, sizeof format, "%%%s", lean_string_cstr(lean_array_get_core(formats, i)));
    if (!strftime(buf, sizeof buf, format, &tm)) snprintf(buf, sizeof buf, "%s", format);
    a = lean_array_push(a, lean_mk_string(buf));
  }
  return lean_io_result_mk_ok(a);
}
LEAN_EXPORT lean_obj_res leansudo_iolog_prepare(b_lean_obj_arg dir, b_lean_obj_arg user,
    b_lean_obj_arg group, uint32_t mode, uint32_t maxseq, lean_obj_arg world) {
  (void)world;
  memset(&logstate, 0, sizeof logstate);
  for (int i = 0; i < 6; i++) logstate.fd[i] = -1;
  logstate.mode = (mode & 0777) | 0600;
  struct passwd *pw = getpwnam(lean_string_cstr(user));
  if (!pw) { errno = ENOENT; return failure("I/O log owner"); }
  logstate.uid = pw->pw_uid; logstate.gid = pw->pw_gid;
  if (*lean_string_cstr(group)) {
    struct group *gr = getgrnam(lean_string_cstr(group));
    if (!gr) { errno = ENOENT; return failure("I/O log group"); }
    logstate.gid = gr->gr_gid;
  }
  int d = directory(lean_string_cstr(dir));
  if (d < 0) return failure("I/O log directory");
  int fd = openat(d, "seq", O_RDWR | O_CREAT | O_NOFOLLOW | O_CLOEXEC | O_NONBLOCK, 0600);
  int err = errno; close(d); errno = err;
  if (fd < 0) return failure("I/O log sequence");
  struct stat st;
  if (fstat(fd, &st) || !S_ISREG(st.st_mode) || st.st_nlink != 1 || lockf(fd, F_LOCK, 0) ||
      fchown(fd, logstate.uid, logstate.gid) || fchmod(fd, logstate.mode)) goto bad;
  char buf[8] = {0};
  ssize_t n = pread(fd, buf, 7, 0);
  if (n < 0) goto bad;
  unsigned long value = 0;
  if (n) {
    if (n != 6 && (n != 7 || buf[6] != '\n')) { errno = EINVAL; goto bad; }
    for (int i = 0; i < 6; i++) {
      unsigned digit;
      if (buf[i] >= '0' && buf[i] <= '9') digit = (unsigned)(buf[i] - '0');
      else if (buf[i] >= 'A' && buf[i] <= 'Z') digit = (unsigned)(buf[i] - 'A' + 10);
      else if (buf[i] >= 'a' && buf[i] <= 'z') digit = (unsigned)(buf[i] - 'a' + 10);
      else { errno = EINVAL; goto bad; }
      value = value * 36 + digit;
    }
  }
  value = value >= maxseq ? 1 : value + 1;
  unsigned long v = value;
  for (int i = 5; i >= 0; i--) { unsigned dig = v % 36; buf[i] = (char)(dig < 10 ? '0' + dig : 'A' + dig - 10); v /= 36; }
  buf[6] = '\n';
  if (pwrite(fd, buf, 7, 0) != 7 || ftruncate(fd, 7)) goto bad;
  close(fd);
  return lean_io_result_mk_ok(lean_unsigned_to_nat((unsigned)value));
bad:
  err = errno ? errno : EINVAL; close(fd); errno = err;
  return failure("I/O log sequence");
}
LEAN_EXPORT lean_obj_res leansudo_iolog_start(b_lean_obj_arg path, b_lean_obj_arg legacy,
    b_lean_obj_arg json, uint32_t flags, b_lean_obj_arg patterns, lean_obj_arg world) {
  (void)world;
  logstate.compressed = (flags & 32) != 0; logstate.flush = (flags & 64) != 0;
  logstate.ignore = (flags & 128) != 0; logstate.passwords = (flags & 256) != 0;
  if (logstate.compressed && !zlib) {
    zlib = dlopen("libz.so.1", RTLD_NOW | RTLD_LOCAL);
    if (!zlib) { errno = ENOSYS; return failure("I/O log compression"); }
    *(void **)(&z_gzdopen) = dlsym(zlib, "gzdopen"); *(void **)(&z_gzwrite) = dlsym(zlib, "gzwrite");
    *(void **)(&z_gzflush) = dlsym(zlib, "gzflush"); *(void **)(&z_gzclose) = dlsym(zlib, "gzclose");
  }
  if (logstate.compressed && (!z_gzdopen || !z_gzwrite || !z_gzflush || !z_gzclose)) {
    errno = ENOSYS; return failure("I/O log compression ABI");
  }
  if (!logstate.passwords) {
    size_t count = lean_array_size(patterns);
    logstate.patterns = calloc(count ? count : 1, sizeof(regex_t));
    if (!logstate.patterns) return failure("I/O log password filters");
    for (size_t i = 0; i < count; i++) {
      if (regcomp(&logstate.patterns[i], lean_string_cstr(lean_array_get_core(patterns, i)), REG_EXTENDED | REG_NOSUB)) {
        errno = EINVAL; return failure("I/O log password filter");
      }
      logstate.npatterns++;
    }
  }
  int d = directory(lean_string_cstr(path));
  if (d < 0) return failure("I/O log session directory");
  const char *names[] = {"stdin", "stdout", "stderr", "ttyin", "ttyout", "timing"};
  for (int i = 0; i < 2; i++) {
    int fd = log_file(d, i ? "log.json" : "log");
    if (fd < 0) goto bad;
    const char *s = lean_string_cstr(i ? json : legacy);
    int rc = write_all(fd, s, strlen(s)); int err = errno;
    if (close(fd) && !rc) { rc = -1; err = errno; }
    if (rc) { errno = err; goto bad; }
  }
  for (int i = 0; i < 6; i++) {
    if (i < 5 && !(flags & (1u << i))) continue;
    logstate.fd[i] = log_file(d, names[i]);
    if (logstate.fd[i] < 0) goto bad;
    if (logstate.compressed) {
      logstate.gz[i] = z_gzdopen(logstate.fd[i], "wb");
      if (!logstate.gz[i]) { errno = EIO; goto bad; }
    }
  }
  if (clock_gettime(CLOCK_MONOTONIC, &logstate.last)) goto bad;
  close(d); logstate.active = 1;
  return lean_io_result_mk_ok(lean_box(0));
bad: {
  int err = errno; close(d); errno = err;
  return failure("I/O log session files");
}
}
