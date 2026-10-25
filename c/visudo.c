#ifndef _GNU_SOURCE
#define _GNU_SOURCE
#endif
#include <lean/lean.h>
#include <errno.h>
#include <fcntl.h>
#include <stdint.h>
#include <signal.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/wait.h>
#include <unistd.h>

static lean_obj_res visudo_status(int result) {
    return lean_io_result_mk_ok(lean_box_uint32(result < 0 ? errno : 0));
}

static lean_obj_res visudo_number(ssize_t result) {
    int error = result < 0 ? errno : 0;
    lean_object *pair = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(pair, 0, lean_box_uint32(error));
    lean_ctor_set(pair, 1, lean_box_usize(result < 0 ? 0 : (size_t)result));
    return lean_io_result_mk_ok(pair);
}

static lean_obj_res visudo_stat_result(int result, const struct stat *st) {
    int error = result < 0 ? errno : 0;
    lean_object *value;
    if (result < 0) {
        value = lean_alloc_ctor(0, 1, 0);
        lean_ctor_set(value, 0, lean_box_uint32(error));
    } else {
        lean_object *fields = lean_alloc_ctor(0, 8, 0);
        lean_ctor_set(fields, 0, lean_uint64_to_nat(st->st_dev));
        lean_ctor_set(fields, 1, lean_uint64_to_nat(st->st_ino));
        lean_ctor_set(fields, 2, lean_uint64_to_nat(st->st_mode));
        lean_ctor_set(fields, 3, lean_uint64_to_nat(st->st_uid));
        lean_ctor_set(fields, 4, lean_uint64_to_nat(st->st_gid));
        lean_ctor_set(fields, 5, lean_uint64_to_nat(st->st_size));
        lean_ctor_set(fields, 6, lean_uint64_to_nat((uint64_t)st->st_mtim.tv_sec));
        lean_ctor_set(fields, 7, lean_uint64_to_nat(st->st_mtim.tv_nsec));
        value = lean_alloc_ctor(1, 1, 0);
        lean_ctor_set(value, 0, fields);
    }
    return lean_io_result_mk_ok(value);
}

LEAN_EXPORT lean_obj_res leansudo_visudo_errno(uint32_t error) {
    char buffer[1024] = {0};
    const char *message = strerror_r((int)error, buffer, sizeof(buffer));
    return lean_io_result_mk_ok(lean_mk_string_from_bytes(message,
        strnlen(message, sizeof(buffer) - 1)));
}

LEAN_EXPORT lean_obj_res leansudo_visudo_open(b_lean_obj_arg path, uint32_t flags, uint32_t mode) {
    return visudo_number(open(lean_string_cstr(path), flags, mode));
}

LEAN_EXPORT lean_obj_res leansudo_visudo_close(uint32_t fd) {
    return visudo_status(close(fd));
}

LEAN_EXPORT lean_obj_res leansudo_visudo_stat(b_lean_obj_arg path) {
    struct stat st;
    int result = stat(lean_string_cstr(path), &st);
    return visudo_stat_result(result, &st);
}

LEAN_EXPORT lean_obj_res leansudo_visudo_fstat(uint32_t fd) {
    struct stat st;
    int result = fstat(fd, &st);
    return visudo_stat_result(result, &st);
}

LEAN_EXPORT lean_obj_res leansudo_visudo_ofd_lock(uint32_t fd) {
    struct flock lock = { .l_type = F_WRLCK, .l_whence = SEEK_SET };
    return visudo_status(fcntl(fd, F_OFD_SETLK, &lock));
}

LEAN_EXPORT lean_obj_res leansudo_visudo_write(uint32_t fd, b_lean_obj_arg bytes, size_t offset) {
    size_t size = lean_string_size(bytes) - 1;
    if (offset > size) {
        errno = EINVAL;
        return visudo_number(-1);
    }
    return visudo_number(write(fd, lean_string_cstr(bytes) + offset, size - offset));
}

LEAN_EXPORT lean_obj_res leansudo_visudo_sync(uint32_t fd) {
    return visudo_status(fsync(fd));
}

LEAN_EXPORT lean_obj_res leansudo_visudo_unlink(b_lean_obj_arg path) {
    return visudo_status(unlink(lean_string_cstr(path)));
}

LEAN_EXPORT lean_obj_res leansudo_visudo_futimens(uint32_t fd, uint64_t sec, uint64_t nsec) {
    struct timespec times[2] = {
        { .tv_sec = (time_t)sec, .tv_nsec = (long)nsec },
        { .tv_sec = (time_t)sec, .tv_nsec = (long)nsec }
    };
    return visudo_status(futimens(fd, times));
}

LEAN_EXPORT lean_obj_res leansudo_visudo_chown(uint32_t fd, uint32_t uid, uint32_t gid) {
    return visudo_status(fchown(fd, uid, gid));
}

LEAN_EXPORT lean_obj_res leansudo_visudo_chmod(uint32_t fd, uint32_t mode) {
    return visudo_status(fchmod(fd, mode));
}


LEAN_EXPORT lean_obj_res leansudo_visudo_exit(uint32_t status) {
    _exit(status);
}

LEAN_EXPORT lean_obj_res leansudo_visudo_open_max(void) {
    return lean_io_result_mk_ok(lean_box_uint64((uint64_t)sysconf(_SC_OPEN_MAX)));
}

LEAN_EXPORT lean_obj_res leansudo_visudo_raise(uint32_t signo) {
    return lean_io_result_mk_ok(lean_box_uint32(raise(signo)));
}

LEAN_EXPORT uint8_t leansudo_visudo_wait_exited(uint32_t status) {
    return WIFEXITED((int)status);
}

LEAN_EXPORT uint32_t leansudo_visudo_no_uid(lean_obj_arg unit) {
    (void)unit;
    return (uid_t)-1;
}

LEAN_EXPORT uint32_t leansudo_visudo_no_gid(lean_obj_arg unit) {
    (void)unit;
    return (gid_t)-1;
}
