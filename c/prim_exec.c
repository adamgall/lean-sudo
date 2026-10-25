#include "shim.h"
#include <errno.h>
#include <dlfcn.h>
#include <limits.h>
#include <fcntl.h>
#include <signal.h>
#include <unistd.h>
#include <sys/socket.h>
#include <grp.h>
#include <sys/stat.h>
#include <sys/wait.h>
#include <sys/resource.h>
#include <poll.h>
#include <termios.h>
#include <sys/ioctl.h>
#include <utmpx.h>
#include <time.h>
#ifdef __linux__
#include <sys/signalfd.h>
#include <sys/syscall.h>
#include <sys/fsuid.h>
#include <sys/auxv.h>
#include <sys/prctl.h>
#include <sys/ptrace.h>
#include <linux/filter.h>
#include <linux/seccomp.h>
#include <pty.h>
#endif

static sigset_t exec_startup_mask;
static int exec_binary_fd = -1;

__attribute__((constructor(101))) static void exec_block_signals(void) {
  sigset_t all;
  memset(&all, 0xff, sizeof all);
  if (sigprocmask(SIG_SETMASK, &all, &exec_startup_mask) != 0) _exit(1);
}

#ifdef __linux__
__attribute__((constructor(102))) static void exec_pin_binary(void) {
  int fd = open("/proc/self/exe", O_PATH | O_CLOEXEC);
  if (fd < 0) _exit(1);
  exec_binary_fd = fcntl(fd, F_DUPFD_CLOEXEC, 3);
  if (exec_binary_fd < 0) _exit(1);
  close(fd);
}
#endif

LEAN_EXPORT uint32_t ls_exec_rt_min(lean_obj_arg unit) {
  (void)unit;
  return SIGRTMIN;
}

LEAN_EXPORT uint32_t ls_exec_rt_kernel_min(lean_obj_arg unit) {
  (void)unit;
#ifdef __GLIBC__
  return __SIGRTMIN;
#else
  return SIGRTMIN;
#endif
}

LEAN_EXPORT size_t ls_exec_sig_default(lean_obj_arg unit) {
  (void)unit;
  return (size_t)SIG_DFL;
}

LEAN_EXPORT size_t ls_exec_sig_ignore(lean_obj_arg unit) {
  (void)unit;
  return (size_t)SIG_IGN;
}

LEAN_EXPORT lean_obj_res leansudo_prim_exec_signal_fd(uint64_t mask) {
#ifdef __linux__
  sigset_t set = {0};
  memcpy(&set, &mask, sizeof mask);
  int fd = signalfd(-1, &set, SFD_CLOEXEC | SFD_NONBLOCK);
  if (fd < 0) return lean_io_result_mk_error(lean_decode_io_error(errno, NULL));
  return ls_ok(lean_box_uint32((uint32_t)fd));
#else
  (void)mask;
  return lean_io_result_mk_error(lean_decode_io_error(ENOSYS, NULL));
#endif
}

LEAN_EXPORT lean_obj_res leansudo_prim_exec_signal_mask(uint64_t mask) {
  sigset_t set = {0};
  memcpy(&set, &mask, sizeof mask);
  if (sigprocmask(SIG_SETMASK, &set, NULL) != 0)
    return lean_io_result_mk_error(lean_decode_io_error(errno, NULL));
  return ls_unit();
}

LEAN_EXPORT lean_obj_res leansudo_prim_exec_startup_mask(void) {
  uint64_t mask;
  memcpy(&mask, &exec_startup_mask, sizeof mask);
  return ls_ok(lean_box_uint64(mask));
}

LEAN_EXPORT lean_obj_res leansudo_prim_exec_binary_fd(void) {
  return ls_ok(lean_box_uint32((uint32_t)exec_binary_fd));
}

LEAN_EXPORT lean_obj_res leansudo_prim_exec_read(uint32_t fd, uint32_t size) {
  lean_object *bytes = lean_alloc_sarray(1, size, size);
  ssize_t n = read((int)fd, lean_sarray_cptr(bytes), size);
  int error = n < 0 ? errno : 0;
  lean_sarray_set_size(bytes, n < 0 ? 0 : (size_t)n);
  return ls_ok(ls_pair(lean_box_uint32((uint32_t)error), bytes));
}

LEAN_EXPORT lean_obj_res leansudo_prim_exec_write(uint32_t fd, b_lean_obj_arg bytes,
    uint32_t offset, uint32_t size) {
  size_t length = lean_sarray_size(bytes);
  if ((size_t)offset > length || (size_t)size > length - (size_t)offset)
    return ls_ok(ls_pair(lean_box_uint32(EINVAL), lean_box_uint32(0)));
  ssize_t n = write((int)fd, lean_sarray_cptr(bytes) + offset, size);
  return ls_ok(ls_pair(lean_box_uint32(n < 0 ? (uint32_t)errno : 0),
      lean_box_uint32(n < 0 ? 0 : (uint32_t)n)));
}

LEAN_EXPORT lean_obj_res leansudo_prim_exec_close(uint32_t fd) {
  if (close((int)fd) != 0)
    return lean_io_result_mk_error(lean_decode_io_error(errno, NULL));
  return ls_unit();
}

LEAN_EXPORT lean_obj_res leansudo_prim_exec_strerror(uint32_t error) {
  char buffer[1024];
#if defined(__GLIBC__) && defined(_GNU_SOURCE)
  return ls_ok(lean_mk_string(strerror_r((int)error, buffer, sizeof buffer)));
#else
  int result = strerror_r((int)error, buffer, sizeof buffer);
  if (result != 0)
    return lean_io_result_mk_error(lean_decode_io_error(result < 0 ? errno : result, NULL));
  return ls_ok(lean_mk_string(buffer));
#endif
}

LEAN_EXPORT lean_obj_res leansudo_prim_exec_open(b_lean_obj_arg path, uint32_t flags,
    uint32_t mode) {
  int fd = open(lean_string_cstr(path), (int)flags, (mode_t)mode);
  return ls_ok(lean_box_uint64(fd < 0 ? (uint64_t)-(int64_t)errno : (uint64_t)fd));
}

LEAN_EXPORT lean_obj_res leansudo_prim_exec_fcntl(uint32_t fd, uint32_t op,
    uint32_t arg) {
  int result = fcntl((int)fd, (int)op, (int)arg);
  return ls_ok(lean_box_uint64(result < 0 ? (uint64_t)-(int64_t)errno : (uint64_t)result));
}

LEAN_EXPORT lean_obj_res leansudo_prim_exec_dup2(uint32_t from, uint32_t to) {
  if (dup2((int)from, (int)to) < 0)
    return lean_io_result_mk_error(lean_decode_io_error(errno, NULL));
  return ls_unit();
}

LEAN_EXPORT lean_obj_res leansudo_prim_exec_pipe(uint32_t flags) {
  int fds[2];
#ifdef __linux__
  if (pipe2(fds, (int)flags) != 0)
    return lean_io_result_mk_error(lean_decode_io_error(errno, NULL));
#else
  (void)flags;
  if (pipe(fds) != 0)
    return lean_io_result_mk_error(lean_decode_io_error(errno, NULL));
#endif
  return ls_ok(ls_pair(lean_box_uint32((uint32_t)fds[0]),
      lean_box_uint32((uint32_t)fds[1])));
}

LEAN_EXPORT lean_obj_res leansudo_prim_exec_socketpair(void) {
  int fds[2];
#ifdef __linux__
  if (socketpair(AF_UNIX, SOCK_STREAM | SOCK_CLOEXEC, 0, fds) != 0)
    return lean_io_result_mk_error(lean_decode_io_error(errno, NULL));
#else
  if (socketpair(AF_UNIX, SOCK_STREAM, 0, fds) != 0)
    return lean_io_result_mk_error(lean_decode_io_error(errno, NULL));
#endif
  return ls_ok(ls_pair(lean_box_uint32((uint32_t)fds[0]),
      lean_box_uint32((uint32_t)fds[1])));
}

LEAN_EXPORT lean_obj_res leansudo_prim_exec_peer_credentials(uint32_t fd) {
#ifdef __linux__
  struct ucred cred;
  socklen_t length = sizeof cred;
  if (getsockopt((int)fd, SOL_SOCKET, SO_PEERCRED, &cred, &length) != 0)
    return lean_io_result_mk_error(lean_decode_io_error(errno, NULL));
  if (length != sizeof cred) return lean_io_result_mk_error(lean_decode_io_error(EINVAL, NULL));
  return ls_ok(ls_pair(lean_box_uint32((uint32_t)cred.pid),
      ls_pair(lean_box_uint32((uint32_t)cred.uid), lean_box_uint32((uint32_t)cred.gid))));
#else
  (void)fd;
  return lean_io_result_mk_error(lean_decode_io_error(ENOSYS, NULL));
#endif
}

LEAN_EXPORT lean_obj_res leansudo_prim_exec_fork_helper(uint32_t executable, uint32_t plan,
    b_lean_obj_arg keep) {
  char *argv[] = {(char *)"sudo", (char *)"--lean-sudo-helper", NULL};
  extern char **environ;
  size_t count = lean_array_size(keep);
  if (count > 1048576)
    return lean_io_result_mk_error(lean_decode_io_error(EINVAL, NULL));
  pid_t (*fork_process)(void) = dlsym(RTLD_DEFAULT, "_Fork");
  if (!fork_process) return lean_io_result_mk_error(lean_decode_io_error(ENOSYS, NULL));
  int *fds = calloc(count + 1, sizeof *fds);
  if (!fds) return lean_io_result_mk_error(lean_decode_io_error(ENOMEM, NULL));
  for (size_t i = 0; i < count; i++)
    fds[i] = (int)lean_unbox_uint32(lean_array_get_core(keep, i));
  pid_t pid = fork_process();
  if (pid == 0) {
    for (size_t i = 0; i < count; i++)
      if (fcntl(fds[i], F_SETFD, 0) != 0) _exit(127);
    if (dup2((int)plan, 63) != 63) _exit(127);
    fexecve((int)executable, argv, environ);
    _exit(127);
  }
  int error = errno;
  free(fds);
  if (pid < 0) return lean_io_result_mk_error(lean_decode_io_error(error, NULL));
  return ls_ok(lean_box_uint32((uint32_t)pid));
}

LEAN_EXPORT lean_obj_res leansudo_prim_exec_getpid(void) {
  return ls_ok(lean_box_uint32((uint32_t)getpid()));
}

LEAN_EXPORT lean_obj_res leansudo_prim_exec_getppid(void) {
  return ls_ok(lean_box_uint32((uint32_t)getppid()));
}

LEAN_EXPORT lean_obj_res leansudo_prim_exec_getuid(void) {
  return ls_ok(lean_box_uint32((uint32_t)getuid()));
}

LEAN_EXPORT lean_obj_res leansudo_prim_exec_geteuid(void) {
  return ls_ok(lean_box_uint32((uint32_t)geteuid()));
}

LEAN_EXPORT lean_obj_res leansudo_prim_exec_getgid(void) {
  return ls_ok(lean_box_uint32((uint32_t)getgid()));
}

LEAN_EXPORT lean_obj_res leansudo_prim_exec_stat(b_lean_obj_arg path) {
  struct stat st;
  if (stat(lean_string_cstr(path), &st) != 0)
    return lean_io_result_mk_error(lean_decode_io_error(errno, NULL));
  lean_object *out = lean_alloc_array(3, 3);
  lean_array_set_core(out, 0, lean_box_uint64((uint64_t)st.st_dev));
  lean_array_set_core(out, 1, lean_box_uint64((uint64_t)st.st_ino));
  lean_array_set_core(out, 2, lean_box_uint64((uint64_t)st.st_mode));
  return ls_ok(out);
}

LEAN_EXPORT lean_obj_res leansudo_prim_exec_fstat(uint32_t fd) {
  struct stat st;
  if (fstat((int)fd, &st) != 0)
    return lean_io_result_mk_error(lean_decode_io_error(errno, NULL));
  lean_object *out = lean_alloc_array(3, 3);
  lean_array_set_core(out, 0, lean_box_uint64((uint64_t)st.st_dev));
  lean_array_set_core(out, 1, lean_box_uint64((uint64_t)st.st_ino));
  lean_array_set_core(out, 2, lean_box_uint64((uint64_t)st.st_mode));
  return ls_ok(out);
}

LEAN_EXPORT lean_obj_res leansudo_prim_exec_getresuid(void) {
#ifdef __linux__
  uid_t r, e, s;
  if (getresuid(&r, &e, &s) != 0)
    return lean_io_result_mk_error(lean_decode_io_error(errno, NULL));
  return ls_ok(ls_pair(lean_box_uint32(r), ls_pair(lean_box_uint32(e), lean_box_uint32(s))));
#else
  return lean_io_result_mk_error(lean_decode_io_error(ENOSYS, NULL));
#endif
}

LEAN_EXPORT lean_obj_res leansudo_prim_exec_getresgid(void) {
#ifdef __linux__
  gid_t r, e, s;
  if (getresgid(&r, &e, &s) != 0)
    return lean_io_result_mk_error(lean_decode_io_error(errno, NULL));
  return ls_ok(ls_pair(lean_box_uint32(r), ls_pair(lean_box_uint32(e), lean_box_uint32(s))));
#else
  return lean_io_result_mk_error(lean_decode_io_error(ENOSYS, NULL));
#endif
}

LEAN_EXPORT lean_obj_res leansudo_prim_exec_setresuid(uint32_t r, uint32_t e, uint32_t s) {
#ifdef __linux__
  if (setresuid(r, e, s) != 0)
    return lean_io_result_mk_error(lean_decode_io_error(errno, NULL));
  return ls_unit();
#else
  (void)r; (void)e; (void)s;
  return lean_io_result_mk_error(lean_decode_io_error(ENOSYS, NULL));
#endif
}

LEAN_EXPORT lean_obj_res leansudo_prim_exec_thread_setresuid(uint32_t r, uint32_t e,
    uint32_t s) {
#ifdef __linux__
  if (syscall(SYS_setresuid, r, e, s) != 0)
    return lean_io_result_mk_error(lean_decode_io_error(errno, NULL));
  return ls_unit();
#else
  (void)r; (void)e; (void)s;
  return lean_io_result_mk_error(lean_decode_io_error(ENOSYS, NULL));
#endif
}

LEAN_EXPORT lean_obj_res leansudo_prim_exec_setresgid(uint32_t r, uint32_t e, uint32_t s) {
#ifdef __linux__
  if (setresgid(r, e, s) != 0)
    return lean_io_result_mk_error(lean_decode_io_error(errno, NULL));
  return ls_unit();
#else
  (void)r; (void)e; (void)s;
  return lean_io_result_mk_error(lean_decode_io_error(ENOSYS, NULL));
#endif
}

LEAN_EXPORT lean_obj_res leansudo_prim_exec_setuid(uint32_t uid) {
  return ls_ok(lean_box_uint32(setuid(uid) == 0 ? 0 : (uint32_t)errno));
}

LEAN_EXPORT lean_obj_res leansudo_prim_exec_setgid(uint32_t gid) {
  return ls_ok(lean_box_uint32(setgid(gid) == 0 ? 0 : (uint32_t)errno));
}

LEAN_EXPORT lean_obj_res leansudo_prim_exec_fsuid(void) {
#ifdef __linux__
  return ls_ok(lean_box_uint32((uint32_t)setfsuid((uid_t)-1)));
#else
  return lean_io_result_mk_error(lean_decode_io_error(ENOSYS, NULL));
#endif
}

LEAN_EXPORT lean_obj_res leansudo_prim_exec_fsgid(void) {
#ifdef __linux__
  return ls_ok(lean_box_uint32((uint32_t)setfsgid((gid_t)-1)));
#else
  return lean_io_result_mk_error(lean_decode_io_error(ENOSYS, NULL));
#endif
}

LEAN_EXPORT lean_obj_res leansudo_prim_exec_getgroups(uint32_t capacity) {
  if (capacity > 65536)
    return lean_io_result_mk_error(lean_decode_io_error(E2BIG, NULL));
  gid_t *groups = capacity ? malloc((size_t)capacity * sizeof *groups) : NULL;
  if (capacity && !groups)
    return lean_io_result_mk_error(lean_decode_io_error(ENOMEM, NULL));
  int n = getgroups((int)capacity, groups);
  if (n < 0) {
    int error = errno;
    free(groups);
    return lean_io_result_mk_error(lean_decode_io_error(error, NULL));
  }
  lean_object *out = lean_alloc_array(capacity ? (size_t)n : 0, capacity ? (size_t)n : 0);
  for (int i = 0; capacity && i < n; i++)
    lean_array_set_core(out, (size_t)i, lean_box_uint32(groups[i]));
  free(groups);
  return ls_ok(ls_pair(lean_box_uint32((uint32_t)n), out));
}

LEAN_EXPORT lean_obj_res leansudo_prim_exec_setgroups(b_lean_obj_arg array) {
  size_t n = lean_array_size(array);
  if (n > 65536 || n > SIZE_MAX / sizeof(gid_t))
    return lean_io_result_mk_error(lean_decode_io_error(E2BIG, NULL));
  gid_t *groups = n ? malloc(n * sizeof *groups) : NULL;
  if (n && !groups)
    return lean_io_result_mk_error(lean_decode_io_error(ENOMEM, NULL));
  for (size_t i = 0; i < n; i++) groups[i] = lean_unbox_uint32(lean_array_get_core(array, i));
  int result = setgroups(n, groups);
  int error = result != 0 ? errno : 0;
  free(groups);
  if (error != 0) return lean_io_result_mk_error(lean_decode_io_error(error, NULL));
  return ls_unit();
}

LEAN_EXPORT lean_obj_res leansudo_prim_exec_thread_setgroups(b_lean_obj_arg array) {
#ifdef __linux__
  size_t n = lean_array_size(array);
  if (n > 65536)
    return lean_io_result_mk_error(lean_decode_io_error(E2BIG, NULL));
  gid_t *groups = n ? malloc(n * sizeof *groups) : NULL;
  if (n && !groups)
    return lean_io_result_mk_error(lean_decode_io_error(ENOMEM, NULL));
  for (size_t i = 0; i < n; i++) groups[i] = lean_unbox_uint32(lean_array_get_core(array, i));
  long result = syscall(SYS_setgroups, n, groups);
  int error = result != 0 ? errno : 0;
  free(groups);
  if (error != 0) return lean_io_result_mk_error(lean_decode_io_error(error, NULL));
  return ls_unit();
#else
  (void)array;
  return lean_io_result_mk_error(lean_decode_io_error(ENOSYS, NULL));
#endif
}

LEAN_EXPORT lean_obj_res leansudo_prim_exec_thread_setresgid(uint32_t r, uint32_t e,
    uint32_t s) {
#ifdef __linux__
  if (syscall(SYS_setresgid, r, e, s) != 0)
    return lean_io_result_mk_error(lean_decode_io_error(errno, NULL));
  return ls_unit();
#else
  (void)r; (void)e; (void)s;
  return lean_io_result_mk_error(lean_decode_io_error(ENOSYS, NULL));
#endif
}

LEAN_EXPORT lean_obj_res leansudo_prim_exec_thread_setuid(uint32_t uid) {
#ifdef __linux__
  return ls_ok(lean_box_uint32(syscall(SYS_setuid, uid) == 0 ? 0 : (uint32_t)errno));
#else
  (void)uid;
  return ls_ok(lean_box_uint32(ENOSYS));
#endif
}

LEAN_EXPORT lean_obj_res leansudo_prim_exec_thread_setgid(uint32_t gid) {
#ifdef __linux__
  return ls_ok(lean_box_uint32(syscall(SYS_setgid, gid) == 0 ? 0 : (uint32_t)errno));
#else
  (void)gid;
  return ls_ok(lean_box_uint32(ENOSYS));
#endif
}

LEAN_EXPORT lean_obj_res leansudo_prim_exec_waitpid(uint32_t pid, uint32_t flags) {
  int status = 0;
  pid_t result = waitpid((pid_t)pid, &status, (int)flags);
  return ls_ok(ls_pair(lean_box_uint64(result < 0 ? (uint64_t)-(int64_t)errno :
      (uint64_t)result), lean_box_uint32((uint32_t)status)));
}

LEAN_EXPORT lean_obj_res leansudo_prim_exec_execve(b_lean_obj_arg path,
    b_lean_obj_arg args, b_lean_obj_arg env) {
  size_t argc = lean_array_size(args), envc = lean_array_size(env);
  if (argc > 65536 || envc > 65536 || argc > SIZE_MAX - envc - 2 ||
      argc + envc + 2 > SIZE_MAX / sizeof(char *))
    return ls_ok(lean_box_uint32(E2BIG));
  char **argv = malloc((argc + envc + 2) * sizeof *argv);
  if (!argv) return ls_ok(lean_box_uint32(ENOMEM));
  char **envp = argv + argc + 1;
  for (size_t i = 0; i < argc; i++)
    argv[i] = (char *)lean_string_cstr(lean_array_get_core(args, i));
  for (size_t i = 0; i < envc; i++)
    envp[i] = (char *)lean_string_cstr(lean_array_get_core(env, i));
  argv[argc] = NULL;
  envp[envc] = NULL;
  execve(lean_string_cstr(path), argv, envp);
  int error = errno;
  free(argv);
  return ls_ok(lean_box_uint32((uint32_t)error));
}

LEAN_EXPORT lean_obj_res leansudo_prim_exec_fexecve(uint32_t fd,
    b_lean_obj_arg args, b_lean_obj_arg env) {
  size_t argc = lean_array_size(args), envc = lean_array_size(env);
  if (argc > 65536 || envc > 65536 || argc > SIZE_MAX - envc - 2 ||
      argc + envc + 2 > SIZE_MAX / sizeof(char *))
    return ls_ok(lean_box_uint32(E2BIG));
  char **argv = malloc((argc + envc + 2) * sizeof *argv);
  if (!argv) return ls_ok(lean_box_uint32(ENOMEM));
  char **envp = argv + argc + 1;
  for (size_t i = 0; i < argc; i++)
    argv[i] = (char *)lean_string_cstr(lean_array_get_core(args, i));
  for (size_t i = 0; i < envc; i++)
    envp[i] = (char *)lean_string_cstr(lean_array_get_core(env, i));
  argv[argc] = NULL;
  envp[envc] = NULL;
  fexecve((int)fd, argv, envp);
  int error = errno;
  free(argv);
  return ls_ok(lean_box_uint32((uint32_t)error));
}

LEAN_EXPORT lean_obj_res leansudo_prim_exec_close_range(uint32_t first, uint32_t last,
    uint32_t flags) {
#ifdef __linux__
  int result = (int)syscall(SYS_close_range, first, last, flags);
  return ls_ok(lean_box_uint32(result < 0 ? (uint32_t)errno : 0));
#else
  (void)first; (void)last; (void)flags;
  return ls_ok(lean_box_uint32(ENOSYS));
#endif
}

LEAN_EXPORT lean_obj_res leansudo_prim_exec_kill(uint32_t pid, uint32_t signal) {
  return ls_ok(lean_box_uint32(kill((pid_t)pid, (int)signal) == 0 ? 0 : (uint32_t)errno));
}

LEAN_EXPORT lean_obj_res leansudo_prim_exec_exit(uint32_t code) {
  _exit((int)code);
}

LEAN_EXPORT lean_obj_res leansudo_prim_exec_chdir(b_lean_obj_arg path) {
  return ls_ok(lean_box_uint32(chdir(lean_string_cstr(path)) == 0 ? 0 : (uint32_t)errno));
}

LEAN_EXPORT lean_obj_res leansudo_prim_exec_chroot(b_lean_obj_arg path) {
  return ls_ok(lean_box_uint32(chroot(lean_string_cstr(path)) == 0 ? 0 : (uint32_t)errno));
}

LEAN_EXPORT lean_obj_res leansudo_prim_exec_umask(uint32_t mask) {
  return ls_ok(lean_box_uint32((uint32_t)umask((mode_t)mask)));
}

LEAN_EXPORT lean_obj_res leansudo_prim_exec_getrlimit(uint32_t resource) {
  struct rlimit limit;
  if (getrlimit((int)resource, &limit) != 0)
    return lean_io_result_mk_error(lean_decode_io_error(errno, NULL));
  return ls_ok(ls_pair(lean_box_uint64(limit.rlim_cur), lean_box_uint64(limit.rlim_max)));
}

LEAN_EXPORT lean_obj_res leansudo_prim_exec_setrlimit(uint32_t resource,
    uint64_t current, uint64_t maximum) {
  struct rlimit limit = {(rlim_t)current, (rlim_t)maximum};
  int result = setrlimit((int)resource, &limit);
  return ls_ok(lean_box_uint32(result == 0 ? 0 : (uint32_t)errno));
}

LEAN_EXPORT lean_obj_res leansudo_prim_exec_prctl(uint32_t op, uint64_t a, uint64_t b,
    uint64_t c, uint64_t d) {
#ifdef __linux__
  int result = prctl((int)op, (unsigned long)a, (unsigned long)b,
      (unsigned long)c, (unsigned long)d);
  return ls_ok(lean_box_uint64(result < 0 ? (uint64_t)-(int64_t)errno : (uint64_t)result));
#else
  (void)op; (void)a; (void)b; (void)c; (void)d;
  return ls_ok(lean_box_uint64((uint64_t)-(int64_t)ENOSYS));
#endif
}

LEAN_EXPORT lean_obj_res leansudo_prim_exec_seccomp(b_lean_obj_arg bytes) {
#ifdef __linux__
  size_t size = lean_sarray_size(bytes);
  if (size % sizeof(struct sock_filter) != 0 ||
      size / sizeof(struct sock_filter) > USHRT_MAX)
    return ls_ok(lean_box_uint32(EINVAL));
  struct sock_fprog program = {
    (unsigned short)(size / sizeof(struct sock_filter)),
    (struct sock_filter *)lean_sarray_cptr(bytes)
  };
  int result = (int)syscall(SYS_seccomp, SECCOMP_SET_MODE_FILTER, 0, &program);
  return ls_ok(lean_box_uint32(result == 0 ? 0 : (uint32_t)errno));
#else
  (void)bytes;
  return ls_ok(lean_box_uint32(ENOSYS));
#endif
}

LEAN_EXPORT lean_obj_res leansudo_prim_exec_signal_action(uint32_t signal, size_t handler,
    uint32_t flags, uint64_t mask, uint8_t query) {
  struct sigaction action = {0}, old = {0};
  action.sa_handler = (void (*)(int))handler;
  action.sa_flags = (int)flags;
  size_t mask_size = sizeof action.sa_mask < sizeof mask ? sizeof action.sa_mask : sizeof mask;
  memcpy(&action.sa_mask, &mask, mask_size);
  int result = sigaction((int)signal, query ? NULL : &action, &old);
  int error = result != 0 ? errno : 0;
  uint64_t old_handler = 0, old_flags = 0, old_mask = 0;
  if (result == 0) {
    old_handler = (uint64_t)(uintptr_t)old.sa_handler;
    old_flags = (uint32_t)old.sa_flags;
    memcpy(&old_mask, &old.sa_mask, mask_size);
  }
  lean_object *out = lean_alloc_array(4, 4);
  lean_array_set_core(out, 0, lean_box_uint64((uint64_t)error));
  lean_array_set_core(out, 1, lean_box_uint64(old_handler));
  lean_array_set_core(out, 2, lean_box_uint64(old_flags));
  lean_array_set_core(out, 3, lean_box_uint64(old_mask));
  return ls_ok(out);
}

LEAN_EXPORT lean_obj_res leansudo_prim_exec_raise(uint32_t signal) {
  return ls_ok(lean_box_uint32((uint32_t)raise((int)signal)));
}

LEAN_EXPORT lean_obj_res leansudo_prim_exec_setsid(void) {
  pid_t result = setsid();
  return ls_ok(lean_box_uint64(result < 0 ? (uint64_t)-(int64_t)errno : (uint64_t)result));
}

LEAN_EXPORT lean_obj_res leansudo_prim_exec_setpgid(uint32_t pid, uint32_t group) {
  return ls_ok(lean_box_uint32(setpgid((pid_t)pid, (pid_t)group) == 0 ? 0 : (uint32_t)errno));
}

LEAN_EXPORT lean_obj_res leansudo_prim_exec_getpgid(uint32_t pid) {
  pid_t result = getpgid((pid_t)pid);
  return ls_ok(lean_box_uint64(result < 0 ? (uint64_t)-(int64_t)errno : (uint64_t)result));
}

LEAN_EXPORT lean_obj_res leansudo_prim_exec_getsid(uint32_t pid) {
  pid_t result = getsid((pid_t)pid);
  return ls_ok(lean_box_uint64(result < 0 ? (uint64_t)-(int64_t)errno : (uint64_t)result));
}

LEAN_EXPORT lean_obj_res leansudo_prim_exec_poll(b_lean_obj_arg array, uint32_t timeout) {
  size_t n = lean_array_size(array);
  if (n > 65536 || n > SIZE_MAX / sizeof(struct pollfd))
    return ls_ok(ls_pair(lean_box_uint32(E2BIG), lean_alloc_array(0, 0)));
  struct pollfd *fds = n ? malloc(n * sizeof *fds) : NULL;
  if (n && !fds)
    return ls_ok(ls_pair(lean_box_uint32(ENOMEM), lean_alloc_array(0, 0)));
  for (size_t i = 0; i < n; i++) {
    b_lean_obj_arg pair = lean_array_get_core(array, i);
    fds[i] = (struct pollfd){(int)lean_unbox_uint32(lean_ctor_get(pair, 0)),
      (short)lean_unbox_uint32(lean_ctor_get(pair, 1)), 0};
  }
  int result = poll(fds, (nfds_t)n, (int)timeout);
  int error = result < 0 ? errno : 0;
  lean_object *out = lean_alloc_array(n, n);
  for (size_t i = 0; i < n; i++)
    lean_array_set_core(out, i, lean_box_uint32((uint16_t)fds[i].revents));
  free(fds);
  return ls_ok(ls_pair(lean_box_uint32((uint32_t)error), out));
}

LEAN_EXPORT lean_obj_res leansudo_prim_exec_isatty(uint32_t fd) {
  return ls_ok(lean_box(isatty((int)fd) == 1));
}

LEAN_EXPORT lean_obj_res leansudo_prim_exec_tcgetattr(uint32_t fd) {
  struct termios value;
  if (tcgetattr((int)fd, &value) != 0)
    return lean_io_result_mk_error(lean_decode_io_error(errno, NULL));
  lean_object *bytes = lean_alloc_sarray(1, sizeof value, sizeof value);
  memcpy(lean_sarray_cptr(bytes), &value, sizeof value);
  return ls_ok(bytes);
}

LEAN_EXPORT lean_obj_res leansudo_prim_exec_cfmakeraw(b_lean_obj_arg bytes) {
  struct termios value;
  if (lean_sarray_size(bytes) != sizeof value)
    return lean_io_result_mk_error(lean_decode_io_error(EINVAL, NULL));
  memcpy(&value, lean_sarray_cptr(bytes), sizeof value);
  cfmakeraw(&value);
  lean_object *out = lean_alloc_sarray(1, sizeof value, sizeof value);
  memcpy(lean_sarray_cptr(out), &value, sizeof value);
  return ls_ok(out);
}

LEAN_EXPORT lean_obj_res leansudo_prim_exec_tcsetattr(uint32_t fd, uint32_t action,
    b_lean_obj_arg bytes) {
  if (lean_sarray_size(bytes) != sizeof(struct termios))
    return ls_ok(lean_box_uint32(EINVAL));
  int result = tcsetattr((int)fd, (int)action, (const struct termios *)lean_sarray_cptr(bytes));
  return ls_ok(lean_box_uint32(result == 0 ? 0 : (uint32_t)errno));
}

LEAN_EXPORT lean_obj_res leansudo_prim_exec_tcgetpgrp(uint32_t fd) {
  pid_t result = tcgetpgrp((int)fd);
  return ls_ok(lean_box_uint64(result < 0 ? (uint64_t)-(int64_t)errno : (uint64_t)result));
}

LEAN_EXPORT lean_obj_res leansudo_prim_exec_tcsetpgrp(uint32_t fd, uint32_t group) {
  return ls_ok(lean_box_uint32(tcsetpgrp((int)fd, (pid_t)group) == 0 ? 0 : (uint32_t)errno));
}

LEAN_EXPORT lean_obj_res leansudo_prim_exec_winsize(uint32_t fd) {
  struct winsize value = {0};
  if (ioctl((int)fd, TIOCGWINSZ, &value) != 0)
    return lean_io_result_mk_error(lean_decode_io_error(errno, NULL));
  return ls_ok(ls_pair(lean_box_uint32(value.ws_row), lean_box_uint32(value.ws_col)));
}

LEAN_EXPORT lean_obj_res leansudo_prim_exec_set_winsize(uint32_t fd, uint32_t rows,
    uint32_t cols) {
  struct winsize value = {(unsigned short)rows, (unsigned short)cols, 0, 0};
  return ls_ok(lean_box_uint32(ioctl((int)fd, TIOCSWINSZ, &value) == 0 ? 0 : (uint32_t)errno));
}

LEAN_EXPORT lean_obj_res leansudo_prim_exec_ctty(uint32_t fd) {
  return ls_ok(lean_box_uint32(ioctl((int)fd, TIOCSCTTY, 0) == 0 ? 0 : (uint32_t)errno));
}

LEAN_EXPORT lean_obj_res leansudo_prim_exec_openpty(b_lean_obj_arg bytes,
    uint32_t rows, uint32_t cols) {
#ifdef __linux__
  if (lean_sarray_size(bytes) != sizeof(struct termios))
    return lean_io_result_mk_error(lean_decode_io_error(EINVAL, NULL));
  int master, slave;
  struct winsize size = {(unsigned short)rows, (unsigned short)cols, 0, 0};
  if (openpty(&master, &slave, NULL, (struct termios *)lean_sarray_cptr(bytes), &size) != 0)
    return lean_io_result_mk_error(lean_decode_io_error(errno, NULL));
  return ls_ok(ls_pair(lean_box_uint32((uint32_t)master), lean_box_uint32((uint32_t)slave)));
#else
  (void)bytes; (void)rows; (void)cols;
  return lean_io_result_mk_error(lean_decode_io_error(ENOSYS, NULL));
#endif
}

LEAN_EXPORT lean_obj_res leansudo_prim_exec_utmp_start(void) {
  setutxent();
  return ls_unit();
}

LEAN_EXPORT lean_obj_res leansudo_prim_exec_utmp_end(void) {
  endutxent();
  return ls_unit();
}

LEAN_EXPORT lean_obj_res leansudo_prim_exec_utmp_get(b_lean_obj_arg bytes) {
  if (lean_sarray_size(bytes) != sizeof(struct utmpx))
    return lean_io_result_mk_error(lean_decode_io_error(EINVAL, NULL));
  struct utmpx *entry = getutxline((const struct utmpx *)lean_sarray_cptr(bytes));
  if (!entry) return ls_ok(lean_box(0));
  lean_object *out = lean_alloc_sarray(1, sizeof *entry, sizeof *entry);
  memcpy(lean_sarray_cptr(out), entry, sizeof *entry);
  lean_object *some = lean_alloc_ctor(1, 1, 0);
  lean_ctor_set(some, 0, out);
  return ls_ok(some);
}

LEAN_EXPORT lean_obj_res leansudo_prim_exec_utmp_put(b_lean_obj_arg bytes) {
  if (lean_sarray_size(bytes) != sizeof(struct utmpx))
    return lean_io_result_mk_error(lean_decode_io_error(EINVAL, NULL));
  return ls_ok(lean_box(pututxline((const struct utmpx *)lean_sarray_cptr(bytes)) != NULL));
}

LEAN_EXPORT lean_obj_res leansudo_prim_exec_time(void) {
  return ls_ok(lean_box_uint64((uint64_t)time(NULL)));
}

#define EXEC_K32(name, value) \
  LEAN_EXPORT uint32_t ls_exec_k_##name(lean_obj_arg unit) { \
    (void)unit; return (uint32_t)(value); \
  }
#define EXEC_K64(name, value) \
  LEAN_EXPORT uint64_t ls_exec_k_##name(lean_obj_arg unit) { \
    (void)unit; return (uint64_t)(value); \
  }
#define EXEC_KN(name, value) \
  LEAN_EXPORT lean_obj_res ls_exec_k_##name(lean_obj_arg unit) { \
    (void)unit; return lean_box((size_t)(value)); \
  }
EXEC_K32(O_CLOEXEC, O_CLOEXEC)
EXEC_K32(O_NONBLOCK, O_NONBLOCK)
EXEC_K32(O_NOCTTY, O_NOCTTY)
EXEC_K32(O_RDONLY, O_RDONLY)
EXEC_K32(O_WRONLY, O_WRONLY)
EXEC_K32(O_RDWR, O_RDWR)
EXEC_K32(F_GETFD, F_GETFD)
EXEC_K32(F_SETFD, F_SETFD)
EXEC_K32(FD_CLOEXEC, FD_CLOEXEC)
EXEC_K32(F_GETFL, F_GETFL)
EXEC_K32(F_SETFL, F_SETFL)
EXEC_K32(F_DUPFD_CLOEXEC, F_DUPFD_CLOEXEC)
EXEC_K32(EINTR, EINTR)
EXEC_K32(EAGAIN, EAGAIN)
EXEC_K32(EBADF, EBADF)
EXEC_K32(ENOENT, ENOENT)
EXEC_K32(EINVAL, EINVAL)
EXEC_K32(EIO, EIO)
EXEC_K32(EACCES, EACCES)
EXEC_K32(ECHILD, ECHILD)
EXEC_K32(ENOEXEC, ENOEXEC)
EXEC_K32(EPERM, EPERM)
EXEC_K32(SIGKILL, SIGKILL)
EXEC_K32(SIGSTOP, SIGSTOP)
EXEC_K32(SIGTSTP, SIGTSTP)
EXEC_K32(SIGTTIN, SIGTTIN)
EXEC_K32(SIGTTOU, SIGTTOU)
EXEC_K32(SIGCONT, SIGCONT)
EXEC_K32(SIGCHLD, SIGCHLD)
EXEC_K32(SIGWINCH, SIGWINCH)
EXEC_K32(SIGHUP, SIGHUP)
EXEC_K32(SIGTERM, SIGTERM)
EXEC_K32(SIGINT, SIGINT)
EXEC_K32(SIGQUIT, SIGQUIT)
EXEC_K32(SIGALRM, SIGALRM)
EXEC_K32(SIGUSR1, SIGUSR1)
EXEC_K32(SIGUSR2, SIGUSR2)
EXEC_K32(SIGPIPE, SIGPIPE)
EXEC_KN(NSIG, NSIG)
EXEC_K32(POLLIN, POLLIN)
EXEC_K32(POLLOUT, POLLOUT)
EXEC_K32(POLLHUP, POLLHUP)
EXEC_K32(POLLERR, POLLERR)
EXEC_K32(TCSADRAIN, TCSADRAIN)
EXEC_K32(WNOHANG, WNOHANG)
EXEC_K32(WUNTRACED, WUNTRACED)
EXEC_K32(WCONTINUED, WCONTINUED)
EXEC_K32(RLIMIT_CORE, RLIMIT_CORE)
EXEC_K32(RLIMIT_NPROC, RLIMIT_NPROC)
EXEC_K32(RLIMIT_NOFILE, RLIMIT_NOFILE)
EXEC_K32(RLIMIT_AS, RLIMIT_AS)
EXEC_K32(RLIMIT_CPU, RLIMIT_CPU)
EXEC_K32(RLIMIT_DATA, RLIMIT_DATA)
EXEC_K32(RLIMIT_FSIZE, RLIMIT_FSIZE)
EXEC_K32(RLIMIT_MEMLOCK, RLIMIT_MEMLOCK)
EXEC_K32(RLIMIT_RSS, RLIMIT_RSS)
EXEC_K32(RLIMIT_STACK, RLIMIT_STACK)
EXEC_K64(RLIM_INFINITY, RLIM_INFINITY)
EXEC_K64(S_IFMT, S_IFMT)
EXEC_K64(S_IFREG, S_IFREG)
EXEC_K64(S_IFIFO, S_IFIFO)
EXEC_K64(S_IFSOCK, S_IFSOCK)
EXEC_KN(utmpSize, sizeof(struct utmpx))
EXEC_KN(utmpType, offsetof(struct utmpx, ut_type))
EXEC_KN(utmpTypeSize, sizeof(((struct utmpx *)0)->ut_type))
EXEC_KN(utmpPid, offsetof(struct utmpx, ut_pid))
EXEC_KN(utmpPidSize, sizeof(((struct utmpx *)0)->ut_pid))
EXEC_KN(utmpLine, offsetof(struct utmpx, ut_line))
EXEC_KN(utmpLineSize, sizeof(((struct utmpx *)0)->ut_line))
EXEC_KN(utmpId, offsetof(struct utmpx, ut_id))
EXEC_KN(utmpIdSize, sizeof(((struct utmpx *)0)->ut_id))
EXEC_KN(utmpUser, offsetof(struct utmpx, ut_user))
EXEC_KN(utmpUserSize, sizeof(((struct utmpx *)0)->ut_user))
EXEC_KN(utmpSeconds, offsetof(struct utmpx, ut_tv.tv_sec))
EXEC_KN(utmpSecondsSize, sizeof(((struct utmpx *)0)->ut_tv.tv_sec))
EXEC_KN(utmpMicros, offsetof(struct utmpx, ut_tv.tv_usec))
EXEC_KN(utmpMicrosSize, sizeof(((struct utmpx *)0)->ut_tv.tv_usec))
EXEC_K32(USER_PROCESS, USER_PROCESS)
EXEC_K32(DEAD_PROCESS, DEAD_PROCESS)
#ifdef __linux__
EXEC_KN(utmpTermination, offsetof(struct utmpx, ut_exit.e_termination))
EXEC_KN(utmpTerminationSize, sizeof(((struct utmpx *)0)->ut_exit.e_termination))
EXEC_KN(utmpExit, offsetof(struct utmpx, ut_exit.e_exit))
EXEC_KN(utmpExitSize, sizeof(((struct utmpx *)0)->ut_exit.e_exit))
EXEC_K32(PR_GET_DUMPABLE, PR_GET_DUMPABLE)
EXEC_K32(PR_SET_DUMPABLE, PR_SET_DUMPABLE)
EXEC_K32(RLIMIT_LOCKS, RLIMIT_LOCKS)
EXEC_KN(RLIM_NLIMITS, RLIM_NLIMITS)
EXEC_K32(WALL, __WALL)
EXEC_K32(CLOSE_RANGE_CLOEXEC, CLOSE_RANGE_CLOEXEC)
EXEC_K32(signalInfoSize, sizeof(struct signalfd_siginfo))
EXEC_KN(signalInfoSigno, offsetof(struct signalfd_siginfo, ssi_signo))
EXEC_KN(signalInfoCode, offsetof(struct signalfd_siginfo, ssi_code))
EXEC_KN(signalInfoPid, offsetof(struct signalfd_siginfo, ssi_pid))
EXEC_KN(filterSize, sizeof(struct sock_filter))
#else
EXEC_KN(utmpTermination, 0)
EXEC_KN(utmpTerminationSize, 0)
EXEC_KN(utmpExit, 0)
EXEC_KN(utmpExitSize, 0)
EXEC_K32(PR_GET_DUMPABLE, 0)
EXEC_K32(PR_SET_DUMPABLE, 0)
EXEC_K32(RLIMIT_LOCKS, 0)
EXEC_KN(RLIM_NLIMITS, 0)
EXEC_K32(WALL, 0)
EXEC_K32(CLOSE_RANGE_CLOEXEC, 0)
EXEC_K32(signalInfoSize, 0)
EXEC_KN(signalInfoSigno, 0)
EXEC_KN(signalInfoCode, 0)
EXEC_KN(signalInfoPid, 0)
EXEC_KN(filterSize, 0)
#endif
EXEC_K32(waitSignalMask, 0x7f)
EXEC_K32(waitByteMask, 0xff)
EXEC_K32(waitContinued, 0xffff)
EXEC_K32(waitCore, 0x80)
EXEC_K32(waitShift, 8)
EXEC_K32(littleEndian, __BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__)
EXEC_K32(INT_MAX, INT_MAX)

LEAN_EXPORT lean_obj_res leansudo_prim_exec_fchdir(uint32_t fd) {
  return ls_ok(lean_box_uint32(fchdir((int)fd) == 0 ? 0 : (uint32_t)errno));
}

LEAN_EXPORT lean_obj_res leansudo_prim_exec_clearenv(void) {
  return ls_ok(lean_box_uint32(clearenv() == 0 ? 0 : (uint32_t)errno));
}

LEAN_EXPORT lean_obj_res leansudo_prim_exec_setenv(b_lean_obj_arg name, b_lean_obj_arg value) {
  return ls_ok(lean_box_uint32(setenv(lean_string_cstr(name), lean_string_cstr(value), 1) == 0
      ? 0 : (uint32_t)errno));
}
