#include "shim.h"
#include <errno.h>
#include <fcntl.h>
#include <limits.h>
#include <pthread.h>
#include <signal.h>
#include <stdint.h>
#include <sys/stat.h>
#include <sys/time.h>
#include <time.h>
#include <unistd.h>
#include <string.h>

LEAN_EXPORT lean_obj_res lean_sudo_prim_ts_constants(void) {
    lean_object *value = lean_alloc_ctor(0, 0, 42 * sizeof(uint64_t));
#define TS_CONSTANT(index, constant) \
    lean_ctor_set_uint64(value, (index) * sizeof(uint64_t), (uint64_t)(constant))
    TS_CONSTANT(0, O_RDONLY);
    TS_CONSTANT(1, O_RDWR);
    TS_CONSTANT(2, O_CLOEXEC);
    TS_CONSTANT(3, O_DIRECTORY);
    TS_CONSTANT(4, O_NOFOLLOW);
    TS_CONSTANT(5, O_NONBLOCK);
    TS_CONSTANT(6, O_CREAT);
    TS_CONSTANT(7, (uint32_t)AT_FDCWD);
    TS_CONSTANT(8, EINTR);
    TS_CONSTANT(9, ENOENT);
    TS_CONSTANT(10, EEXIST);
    TS_CONSTANT(11, ENOTDIR);
    TS_CONSTANT(12, EACCES);
    TS_CONSTANT(13, EINVAL);
    TS_CONSTANT(14, EOVERFLOW);
    TS_CONSTANT(15, EBADF);
    TS_CONSTANT(16, EIO);
    TS_CONSTANT(17, ELOOP);
    TS_CONSTANT(18, F_WRLCK);
    TS_CONSTANT(19, F_UNLCK);
    TS_CONSTANT(20, CLOCK_REALTIME);
    TS_CONSTANT(21, CLOCK_BOOTTIME);
    TS_CONSTANT(22, SIGINT);
    TS_CONSTANT(23, SIGQUIT);
    TS_CONSTANT(24, S_IFMT);
    TS_CONSTANT(25, S_IFDIR);
    TS_CONSTANT(26, S_IFREG);
    TS_CONSTANT(27, S_IWGRP);
    TS_CONSTANT(28, S_IWOTH);
    TS_CONSTANT(29, S_IRWXU);
    TS_CONSTANT(30, S_IRWXU | S_IXGRP | S_IXOTH);
    TS_CONSTANT(31, S_IRUSR | S_IWUSR);
    TS_CONSTANT(32, PATH_MAX);
    TS_CONSTANT(33, NAME_MAX);
    TS_CONSTANT(34, INT_MAX);
    TS_CONSTANT(35, (uid_t)-1);
    TS_CONSTANT(36, (gid_t)-1);
    TS_CONSTANT(37, (UINT64_C(1) << (sizeof(off_t) * CHAR_BIT - 1)) - 1);
    TS_CONSTANT(38, (UINT64_C(1) << (sizeof(time_t) * CHAR_BIT - 1)) - 1);
    TS_CONSTANT(39, SSIZE_MAX);
    TS_CONSTANT(40, (uint64_t)-1);
    TS_CONSTANT(41, LONG_MAX);
#undef TS_CONSTANT
    return lean_io_result_mk_ok(value);
}

static lean_obj_res ts_result(lean_object *value) {
    lean_object *result = lean_alloc_ctor(1, 1, 0);
    lean_ctor_set(result, 0, value);
    return lean_io_result_mk_ok(result);
}

static lean_obj_res ts_error(int error) {
    lean_object *result = lean_alloc_ctor(0, 1, 0);
    lean_ctor_set(result, 0, lean_box_uint32((uint32_t)error));
    return lean_io_result_mk_ok(result);
}

LEAN_EXPORT lean_obj_res lean_sudo_prim_ts_error(uint32_t error) {
    char buffer[1024];
    return lean_io_result_mk_ok(lean_mk_string(strerror_r(error, buffer, sizeof buffer)));
}

LEAN_EXPORT lean_obj_res lean_sudo_prim_ts_openat(uint32_t dir, b_lean_obj_arg name,
        uint32_t flags, uint32_t mode) {
    int fd = openat((int)dir, lean_string_cstr(name), (int)flags, (mode_t)mode);
    if (fd < 0) return ts_error(errno);
    return ts_result(lean_box_uint32((uint32_t)fd));
}

LEAN_EXPORT lean_obj_res lean_sudo_prim_ts_mkdirat(uint32_t dir, b_lean_obj_arg name,
        uint32_t mode) {
    if (mkdirat((int)dir, lean_string_cstr(name), (mode_t)mode) != 0) return ts_error(errno);
    return ts_result(lean_box(0));
}

LEAN_EXPORT lean_obj_res lean_sudo_prim_ts_unlinkat(uint32_t dir, b_lean_obj_arg name) {
    if (unlinkat((int)dir, lean_string_cstr(name), 0) != 0) return ts_error(errno);
    return ts_result(lean_box(0));
}

LEAN_EXPORT lean_obj_res lean_sudo_prim_ts_fstat(uint32_t fd) {
    struct stat st;
    if (fstat((int)fd, &st) != 0) return ts_error(errno);
    lean_object *value = lean_alloc_ctor(0, 0, 40);
    lean_ctor_set_uint64(value, 0, (uint64_t)st.st_mode);
    lean_ctor_set_uint64(value, 8, (uint64_t)st.st_uid);
    lean_ctor_set_uint64(value, 16, (uint64_t)st.st_gid);
    lean_ctor_set_uint64(value, 24, (uint64_t)st.st_size);
    lean_ctor_set_uint64(value, 32, (uint64_t)st.st_mtime);
    return ts_result(value);
}

LEAN_EXPORT lean_obj_res lean_sudo_prim_ts_fchmod(uint32_t fd, uint32_t mode) {
    if (fchmod((int)fd, (mode_t)mode) != 0) return ts_error(errno);
    return ts_result(lean_box(0));
}

LEAN_EXPORT lean_obj_res lean_sudo_prim_ts_fchown(uint32_t fd, uint32_t uid,
        uint32_t gid) {
    if (fchown((int)fd, (uid_t)uid, (gid_t)gid) != 0) return ts_error(errno);
    return ts_result(lean_box(0));
}

LEAN_EXPORT lean_obj_res lean_sudo_prim_ts_geteuid(void) {
    return lean_io_result_mk_ok(lean_box_uint32((uint32_t)geteuid()));
}

LEAN_EXPORT lean_obj_res lean_sudo_prim_ts_seteuid(uint32_t uid) {
    if (seteuid((uid_t)uid) != 0) return ts_error(errno);
    return ts_result(lean_box(0));
}

LEAN_EXPORT lean_obj_res lean_sudo_prim_ts_close(uint32_t fd) {
    if (close((int)fd) != 0) return ts_error(errno);
    return ts_result(lean_box(0));
}

LEAN_EXPORT lean_obj_res lean_sudo_prim_ts_pread(uint32_t fd, uint64_t offset,
        uint32_t length) {
    lean_object *bytes = lean_alloc_sarray(1, 0, length);
    ssize_t n = pread((int)fd, lean_sarray_cptr(bytes), length, (off_t)offset);
    if (n < 0) {
        int error = errno;
        lean_dec(bytes);
        return ts_error(error);
    }
    lean_sarray_set_size(bytes, (size_t)n);
    return ts_result(bytes);
}

LEAN_EXPORT lean_obj_res lean_sudo_prim_ts_pwrite(uint32_t fd, uint64_t offset,
        b_lean_obj_arg bytes, uint64_t start, uint64_t length) {
    size_t size = lean_sarray_size(bytes);
    if (start > size || length > size - start) return ts_error(EINVAL);
    ssize_t n = pwrite((int)fd, lean_sarray_cptr(bytes) + start, (size_t)length, (off_t)offset);
    if (n < 0) return ts_error(errno);
    return ts_result(lean_box_uint64((uint64_t)n));
}

LEAN_EXPORT lean_obj_res lean_sudo_prim_ts_truncate(uint32_t fd, uint64_t length) {
    if (ftruncate((int)fd, (off_t)length) != 0) return ts_error(errno);
    return ts_result(lean_box(0));
}

LEAN_EXPORT lean_obj_res lean_sudo_prim_ts_lock(uint32_t fd, uint64_t offset,
        uint64_t length, uint32_t type) {
    struct flock region = { .l_type = (short)type, .l_whence = SEEK_SET,
        .l_start = (off_t)offset, .l_len = (off_t)length };
    if (fcntl((int)fd, F_SETLK, &region) != 0) return ts_error(errno);
    return ts_result(lean_box(0));
}

static volatile sig_atomic_t ts_wait_signal;

static void ts_wait_handler(int signo) {
    ts_wait_signal = signo;
}

LEAN_EXPORT lean_obj_res lean_sudo_prim_ts_wait_lock(uint32_t fd, uint64_t offset,
        uint64_t length, uint32_t type, uint32_t first, uint32_t second) {
    sigset_t interrupts, saved_mask;
    struct sigaction saved_first, saved_second;
    struct sigaction action = { .sa_handler = ts_wait_handler };
    struct flock region = { .l_type = (short)type, .l_whence = SEEK_SET,
        .l_start = (off_t)offset, .l_len = (off_t)length };
    int status = -1, error = 0, caught = 0;
    int first_installed = 0, second_installed = 0;
    if (sigemptyset(&interrupts) != 0 ||
            sigaddset(&interrupts, (int)first) != 0 ||
            sigaddset(&interrupts, (int)second) != 0) {
        error = errno;
        goto result;
    }
    error = pthread_sigmask(SIG_BLOCK, &interrupts, &saved_mask);
    if (error != 0) goto result;
    ts_wait_signal = 0;
    action.sa_mask = interrupts;
    if (sigaction((int)first, &action, &saved_first) != 0) {
        error = errno;
        goto restore;
    }
    first_installed = 1;
    if (sigaction((int)second, &action, &saved_second) != 0) {
        error = errno;
        goto restore;
    }
    second_installed = 1;
    error = pthread_sigmask(SIG_UNBLOCK, &interrupts, NULL);
    if (error != 0) goto restore;
    if (ts_wait_signal == 0) {
        status = fcntl((int)fd, F_SETLKW, &region);
        if (status != 0) error = errno;
    }
restore:
    {
        int restored = pthread_sigmask(SIG_BLOCK, &interrupts, NULL);
        if (restored != 0 && error == 0) error = restored;
        caught = ts_wait_signal;
        if (second_installed && sigaction((int)second, &saved_second, NULL) != 0 &&
                error == 0) error = errno;
        if (first_installed && sigaction((int)first, &saved_first, NULL) != 0 &&
                error == 0) error = errno;
        restored = pthread_sigmask(SIG_SETMASK, &saved_mask, NULL);
        if (restored != 0 && error == 0) error = restored;
    }
result:
    {
        lean_object *value = lean_alloc_ctor(0, 0, 12);
        lean_ctor_set_uint32(value, 0, (uint32_t)status);
        lean_ctor_set_uint32(value, 4, (uint32_t)error);
        lean_ctor_set_uint32(value, 8, (uint32_t)caught);
        return lean_io_result_mk_ok(value);
    }
}

LEAN_EXPORT lean_obj_res lean_sudo_prim_ts_clock(uint32_t clock) {
    struct timespec ts;
    if (clock_gettime((clockid_t)clock, &ts) != 0) return ts_error(errno);
    lean_object *value = lean_alloc_ctor(0, 0, 16);
    lean_ctor_set_uint64(value, 0, (uint64_t)ts.tv_sec);
    lean_ctor_set_uint64(value, 8, (uint64_t)ts.tv_nsec);
    return ts_result(value);
}

LEAN_EXPORT lean_obj_res lean_sudo_prim_ts_timeofday(void) {
    struct timeval tv;
    if (gettimeofday(&tv, NULL) != 0) return ts_error(errno);
    lean_object *value = lean_alloc_ctor(0, 0, 16);
    lean_ctor_set_uint64(value, 0, (uint64_t)tv.tv_sec);
    lean_ctor_set_uint64(value, 8, (uint64_t)tv.tv_usec);
    return ts_result(value);
}

LEAN_EXPORT lean_obj_res lean_sudo_prim_ts_monotonic(void) {
    return lean_io_result_mk_ok(lean_box_uint64((uint64_t)sysconf(_SC_MONOTONIC_CLOCK)));
}

LEAN_EXPORT lean_obj_res lean_sudo_prim_ts_ticks(void) {
    errno = 0;
    long ticks = sysconf(_SC_CLK_TCK);
    if (ticks == -1) return ts_error(errno);
    return ts_result(lean_box_uint64((uint64_t)ticks));
}

LEAN_EXPORT lean_obj_res lean_sudo_prim_ts_getsid(void) {
    pid_t sid = getsid(0);
    if (sid < 0) return ts_error(errno);
    return ts_result(lean_box_uint32((uint32_t)sid));
}

LEAN_EXPORT lean_obj_res lean_sudo_prim_ts_getppid(void) {
    return lean_io_result_mk_ok(lean_box_uint32((uint32_t)getppid()));
}
