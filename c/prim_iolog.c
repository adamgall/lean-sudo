#include "shim.h"
#include <sys/stat.h>
#include <sys/ioctl.h>
#include <fcntl.h>
#include <unistd.h>
#include <time.h>
#include <errno.h>
#include <dlfcn.h>
#include <regex.h>
#include <signal.h>
#include <limits.h>
#define Z_SYNC_FLUSH 2

LEAN_EXPORT lean_obj_res leansudo_iop_constants(void) {
  lean_object *out = lean_alloc_ctor(0, 0, 35 * sizeof(uint32_t));
  lean_ctor_set_uint32(out, 0 * sizeof(uint32_t), O_RDONLY);
  lean_ctor_set_uint32(out, 1 * sizeof(uint32_t), O_WRONLY);
  lean_ctor_set_uint32(out, 2 * sizeof(uint32_t), O_RDWR);
  lean_ctor_set_uint32(out, 3 * sizeof(uint32_t), O_CREAT);
  lean_ctor_set_uint32(out, 4 * sizeof(uint32_t), O_NOFOLLOW);
  lean_ctor_set_uint32(out, 5 * sizeof(uint32_t), O_CLOEXEC);
  lean_ctor_set_uint32(out, 6 * sizeof(uint32_t), O_NONBLOCK);
  lean_ctor_set_uint32(out, 7 * sizeof(uint32_t), O_DIRECTORY);
  lean_ctor_set_uint32(out, 8 * sizeof(uint32_t), O_NOCTTY);
  lean_ctor_set_uint32(out, 9 * sizeof(uint32_t), S_IRWXU);
  lean_ctor_set_uint32(out, 10 * sizeof(uint32_t), S_IRUSR | S_IWUSR);
  lean_ctor_set_uint32(out, 11 * sizeof(uint32_t), S_IRGRP | S_IWGRP);
  lean_ctor_set_uint32(out, 12 * sizeof(uint32_t), S_IXGRP);
  lean_ctor_set_uint32(out, 13 * sizeof(uint32_t), S_IROTH | S_IWOTH);
  lean_ctor_set_uint32(out, 14 * sizeof(uint32_t), S_IXOTH);
  lean_ctor_set_uint32(out, 15 * sizeof(uint32_t), S_IRWXU | S_IRWXG | S_IRWXO);
  lean_ctor_set_uint32(out, 16 * sizeof(uint32_t), S_IFMT);
  lean_ctor_set_uint32(out, 17 * sizeof(uint32_t), S_IFREG);
  lean_ctor_set_uint32(out, 18 * sizeof(uint32_t), S_IWUSR | S_IWGRP | S_IWOTH);
  lean_ctor_set_uint32(out, 19 * sizeof(uint32_t), EEXIST);
  lean_ctor_set_uint32(out, 20 * sizeof(uint32_t), EINTR);
  lean_ctor_set_uint32(out, 21 * sizeof(uint32_t), CLOCK_REALTIME);
  lean_ctor_set_uint32(out, 22 * sizeof(uint32_t), CLOCK_MONOTONIC);
  lean_ctor_set_uint32(out, 23 * sizeof(uint32_t), SIGCONT);
  lean_ctor_set_uint32(out, 24 * sizeof(uint32_t), SIGTSTP);
  lean_ctor_set_uint32(out, 25 * sizeof(uint32_t), SIGTTIN);
  lean_ctor_set_uint32(out, 26 * sizeof(uint32_t), SIGTTOU);
  lean_ctor_set_uint32(out, 27 * sizeof(uint32_t), (uint32_t)AT_FDCWD);
  lean_ctor_set_uint32(out, 28 * sizeof(uint32_t), INT_MAX);
  lean_ctor_set_uint32(out, 29 * sizeof(uint32_t), F_LOCK);
  lean_ctor_set_uint32(out, 30 * sizeof(uint32_t), RTLD_NOW);
  lean_ctor_set_uint32(out, 31 * sizeof(uint32_t), RTLD_LOCAL);
  lean_ctor_set_uint32(out, 32 * sizeof(uint32_t), REG_EXTENDED);
  lean_ctor_set_uint32(out, 33 * sizeof(uint32_t), REG_NOSUB);
  lean_ctor_set_uint32(out, 34 * sizeof(uint32_t), Z_SYNC_FLUSH);
  return ls_ok(out);
}

LEAN_EXPORT lean_obj_res leansudo_iop_openat(uint32_t dir, b_lean_obj_arg path,
    uint32_t flags, uint32_t mode) {
  int fd = openat((int)dir, lean_string_cstr(path), (int)flags, (mode_t)mode);
  uint32_t error = fd < 0 ? (uint32_t)errno : 0;
  return ls_ok(ls_pair(lean_box_uint32(error),
      lean_box_uint32((uint32_t)fd)));
}
LEAN_EXPORT lean_obj_res leansudo_iop_mkdirat(uint32_t dir, b_lean_obj_arg path,
    uint32_t mode) {
  int rc = mkdirat((int)dir, lean_string_cstr(path), (mode_t)mode);
  return ls_ok(lean_box_uint32(rc < 0 ? (uint32_t)errno : 0));
}
LEAN_EXPORT lean_obj_res leansudo_iop_close(uint32_t fd) {
  int rc = close((int)fd);
  return ls_ok(lean_box_uint32(rc < 0 ? (uint32_t)errno : 0));
}
LEAN_EXPORT lean_obj_res leansudo_iop_chown(uint32_t fd, uint32_t uid,
    uint32_t gid) {
  int rc = fchown((int)fd, uid, gid);
  return ls_ok(lean_box_uint32(rc < 0 ? (uint32_t)errno : 0));
}
LEAN_EXPORT lean_obj_res leansudo_iop_chmod(uint32_t fd, uint32_t mode) {
  int rc = fchmod((int)fd, mode);
  return ls_ok(lean_box_uint32(rc < 0 ? (uint32_t)errno : 0));
}
LEAN_EXPORT lean_obj_res leansudo_iop_truncate(uint32_t fd, uint64_t size) {
  int rc = ftruncate((int)fd, (off_t)size);
  return ls_ok(lean_box_uint32(rc < 0 ? (uint32_t)errno : 0));
}
LEAN_EXPORT lean_obj_res leansudo_iop_stat(uint32_t fd) {
  struct stat st;
  int rc = fstat((int)fd, &st);
  uint32_t error = rc < 0 ? (uint32_t)errno : 0;
  return ls_ok(ls_pair(lean_box_uint32(error),
      ls_pair(lean_unsigned_to_nat(error ? 0 : st.st_mode),
      ls_pair(lean_uint64_to_nat(error ? 0 : st.st_nlink),
          lean_unsigned_to_nat(error ? 0 : st.st_uid)))));
}
LEAN_EXPORT lean_obj_res leansudo_iop_lock(uint32_t fd, uint32_t command) {
  int rc = lockf((int)fd, (int)command, 0);
  return ls_ok(lean_box_uint32(rc < 0 ? (uint32_t)errno : 0));
}
LEAN_EXPORT lean_obj_res leansudo_iop_pread(uint32_t fd, uint32_t count,
    uint64_t offset) {
  lean_object *bytes = lean_alloc_sarray(1, count, count);
  ssize_t n = pread((int)fd, lean_sarray_cptr(bytes), count, (off_t)offset);
  uint32_t error = n < 0 ? (uint32_t)errno : 0;
  lean_sarray_set_size(bytes, n < 0 ? 0 : (size_t)n);
  return ls_ok(ls_pair(lean_box_uint32(error), bytes));
}
LEAN_EXPORT lean_obj_res leansudo_iop_pwrite(uint32_t fd, b_lean_obj_arg bytes,
    uint64_t offset) {
  ssize_t n = pwrite((int)fd, lean_sarray_cptr(bytes), lean_sarray_size(bytes), (off_t)offset);
  uint32_t error = n < 0 ? (uint32_t)errno : 0;
  return ls_ok(ls_pair(lean_box_uint32(error),
      lean_uint64_to_nat(n < 0 ? 0 : (uint64_t)n)));
}
LEAN_EXPORT lean_obj_res leansudo_iop_write(uint32_t fd, b_lean_obj_arg bytes,
    uint64_t offset) {
  if (offset > lean_sarray_size(bytes))
    return ls_ok(ls_pair(lean_unsigned_to_nat(0), lean_box_uint32(EINVAL)));
  ssize_t n = write((int)fd, lean_sarray_cptr(bytes) + offset, lean_sarray_size(bytes) - offset);
  if (n < 0) return ls_ok(ls_pair(lean_unsigned_to_nat(0), lean_box_uint32((uint32_t)errno)));
  return ls_ok(ls_pair(lean_uint64_to_nat((uint64_t)n), lean_box_uint32(0)));
}
LEAN_EXPORT lean_obj_res leansudo_iop_error_text(uint32_t error) {
  char buffer[256];
  const char *message = strerror_r((int)error, buffer, sizeof buffer);
  return ls_ok(lean_mk_string_from_bytes(message, strnlen(message, sizeof buffer)));
}
LEAN_EXPORT lean_obj_res leansudo_iop_clock(uint32_t clock) {
  struct timespec now;
  int rc = clock_gettime((clockid_t)clock, &now);
  uint32_t error = rc < 0 ? (uint32_t)errno : 0;
  return ls_ok(ls_pair(lean_box_uint32(error),
      ls_pair(lean_uint64_to_nat(error ? 0 : (uint64_t)now.tv_sec),
          lean_unsigned_to_nat(error ? 0 : (unsigned)now.tv_nsec))));
}
LEAN_EXPORT lean_obj_res leansudo_iop_winsize(uint32_t fd) {
  struct winsize ws;
  int rc = ioctl((int)fd, TIOCGWINSZ, &ws);
  uint32_t error = rc < 0 ? (uint32_t)errno : 0;
  return ls_ok(ls_pair(lean_box_uint32(error),
      ls_pair(lean_unsigned_to_nat(error ? 0 : ws.ws_row),
          lean_unsigned_to_nat(error ? 0 : ws.ws_col))));
}
LEAN_EXPORT lean_obj_res leansudo_iop_dlopen(b_lean_obj_arg path, uint32_t flags) {
  void *handle = dlopen(lean_string_cstr(path), (int)flags);
  return ls_ok(lean_box_uint64((uint64_t)(uintptr_t)handle));
}
LEAN_EXPORT lean_obj_res leansudo_iop_dlsym(uint64_t handle,
    b_lean_obj_arg name) {
  void *symbol = dlsym((void *)(uintptr_t)handle, lean_string_cstr(name));
  return ls_ok(lean_box_uint64((uint64_t)(uintptr_t)symbol));
}
LEAN_EXPORT lean_obj_res leansudo_iop_gzdopen(uint64_t fn, uint32_t fd,
    b_lean_obj_arg mode) {
  void *stream = ((void *(*)(int, const char *))(uintptr_t)fn)((int)fd, lean_string_cstr(mode));
  return ls_ok(lean_box_uint64((uint64_t)(uintptr_t)stream));
}
LEAN_EXPORT lean_obj_res leansudo_iop_gzwrite(uint64_t fn, uint64_t stream,
    b_lean_obj_arg bytes) {
  int n = ((int (*)(void *, const void *, unsigned))(uintptr_t)fn)(
      (void *)(uintptr_t)stream, lean_sarray_cptr(bytes),
      (unsigned)lean_sarray_size(bytes));
  return ls_ok(lean_box_uint32((uint32_t)n));
}
LEAN_EXPORT lean_obj_res leansudo_iop_gzflush(uint64_t fn, uint64_t stream,
    uint32_t mode) {
  int rc = ((int (*)(void *, int))(uintptr_t)fn)((void *)(uintptr_t)stream, (int)mode);
  return ls_ok(lean_box_uint32((uint32_t)rc));
}
LEAN_EXPORT lean_obj_res leansudo_iop_gzclose(uint64_t fn, uint64_t stream) {
  int rc = ((int (*)(void *))(uintptr_t)fn)((void *)(uintptr_t)stream);
  return ls_ok(lean_box_uint32((uint32_t)rc));
}
LEAN_EXPORT lean_obj_res leansudo_iop_regex_alloc(void) {
  void *value = calloc(1, sizeof(regex_t));
  uint32_t error = value ? 0 : (uint32_t)errno;
  return ls_ok(ls_pair(lean_box_uint32(error),
      lean_box_uint64((uint64_t)(uintptr_t)value)));
}
LEAN_EXPORT lean_obj_res leansudo_iop_regex_compile(uint64_t regex,
    b_lean_obj_arg pattern, uint32_t flags) {
  int rc = regcomp((regex_t *)(uintptr_t)regex, lean_string_cstr(pattern), (int)flags);
  return ls_ok(lean_box_uint32((uint32_t)rc));
}
LEAN_EXPORT lean_obj_res leansudo_iop_regex_match(uint64_t regex,
    b_lean_obj_arg bytes, uint32_t flags) {
  int rc = regexec((regex_t *)(uintptr_t)regex, (const char *)lean_sarray_cptr(bytes),
      0, NULL, (int)flags);
  return ls_ok(lean_box_uint32((uint32_t)rc));
}
LEAN_EXPORT lean_obj_res leansudo_iop_regex_release(uint64_t regex) {
  regfree((regex_t *)(uintptr_t)regex);
  return ls_unit();
}
LEAN_EXPORT lean_obj_res leansudo_iop_free(uint64_t pointer) {
  free((void *)(uintptr_t)pointer);
  return ls_unit();
}
