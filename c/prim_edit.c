#include "shim.h"
#include <errno.h>
#include <fcntl.h>
#include <limits.h>
#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <sys/socket.h>
#include <sys/stat.h>
#include <time.h>
#include <unistd.h>

LEAN_EXPORT lean_obj_res leansudo_prim_edit_platform(void) {
    uint64_t values[] = {
        (uint32_t)AT_FDCWD, PATH_MAX, EACCES, EROFS, ENAMETOOLONG, X_OK, W_OK,
        MSG_TRUNC, MSG_CTRUNC, SOL_SOCKET, SCM_RIGHTS,
        CMSG_SPACE(sizeof(int)), CMSG_LEN(sizeof(int)), CMSG_LEN(0),
        offsetof(struct cmsghdr, cmsg_len), sizeof(((struct cmsghdr *)0)->cmsg_len),
        offsetof(struct cmsghdr, cmsg_level), sizeof(((struct cmsghdr *)0)->cmsg_level),
        offsetof(struct cmsghdr, cmsg_type), sizeof(((struct cmsghdr *)0)->cmsg_type),
        sizeof(int), __BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__,
        S_IRUSR | S_IWUSR | S_IRGRP | S_IROTH, S_IRWXU | S_IRWXG | S_IRWXO,
        ((uint64_t)1 << (sizeof(off_t) * CHAR_BIT - 1)) - 1
    };
    lean_object *result = lean_alloc_ctor(0, sizeof(values) / sizeof(values[0]), 0);
    for (size_t i = 0; i < sizeof(values) / sizeof(values[0]); ++i)
        lean_ctor_set(result, i, lean_uint64_to_nat(values[i]));
    return lean_io_result_mk_ok(result);
}

LEAN_EXPORT uint32_t leansudo_prim_edit_default_mask(lean_obj_arg unit) {
    (void)unit;
    return S_IWGRP | S_IWOTH;
}

static lean_obj_res edit_ok(lean_object *value) {
    lean_object *result = lean_alloc_ctor(1, 1, 0);
    lean_ctor_set(result, 0, value);
    return lean_io_result_mk_ok(result);
}

static lean_obj_res edit_error(int error) {
    lean_object *result = lean_alloc_ctor(0, 1, 0);
    lean_ctor_set(result, 0, lean_box_uint32((uint32_t)error));
    return lean_io_result_mk_ok(result);
}

LEAN_EXPORT lean_obj_res leansudo_prim_edit_socketpair(void) {
    int fds[2];
    if (socketpair(AF_UNIX, SOCK_SEQPACKET | SOCK_CLOEXEC, 0, fds)) return edit_error(errno);
    lean_object *pair = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(pair, 0, lean_box_uint32((uint32_t)fds[0]));
    lean_ctor_set(pair, 1, lean_box_uint32((uint32_t)fds[1]));
    return edit_ok(pair);
}

LEAN_EXPORT lean_obj_res leansudo_prim_edit_sendmsg(uint32_t fd,
        b_lean_obj_arg bytes, b_lean_obj_arg control) {
    struct iovec io = { lean_sarray_cptr(bytes), lean_sarray_size(bytes) };
    struct msghdr msg = { .msg_iov = &io, .msg_iovlen = 1,
        .msg_control = lean_sarray_cptr(control), .msg_controllen = lean_sarray_size(control) };
    ssize_t n = sendmsg((int)fd, &msg, MSG_NOSIGNAL);
    if (n < 0) return edit_error(errno);
    return edit_ok(lean_box_uint64((uint64_t)n));
}

LEAN_EXPORT lean_obj_res leansudo_prim_edit_recvmsg(uint32_t fd) {
    lean_object *bytes = lean_alloc_sarray(1, 0, 32768);
    lean_object *control = lean_alloc_sarray(1, 0, CMSG_SPACE(sizeof(int)));
    struct iovec io = { lean_sarray_cptr(bytes), 32768 };
    struct msghdr msg = { .msg_iov = &io, .msg_iovlen = 1,
        .msg_control = lean_sarray_cptr(control), .msg_controllen = CMSG_SPACE(sizeof(int)) };
    ssize_t n = recvmsg((int)fd, &msg, MSG_CMSG_CLOEXEC);
    if (n < 0) {
        int error = errno;
        lean_dec(bytes);
        lean_dec(control);
        return edit_error(error);
    }
    lean_sarray_set_size(bytes, (size_t)n);
    lean_sarray_set_size(control, msg.msg_controllen);
    lean_object *packet = lean_alloc_ctor(0, 2, 4);
    lean_ctor_set(packet, 0, bytes);
    lean_ctor_set(packet, 1, control);
    lean_ctor_set_uint32(packet, 2 * sizeof(void *), (uint32_t)msg.msg_flags);
    return edit_ok(packet);
}

LEAN_EXPORT lean_obj_res leansudo_prim_edit_openat(uint32_t dir, b_lean_obj_arg path,
        uint32_t flags, uint32_t mode) {
    int fd = openat((int)dir, lean_string_cstr(path), (int)flags, (mode_t)mode);
    if (fd < 0) return edit_error(errno);
    return edit_ok(lean_box_uint32((uint32_t)fd));
}

LEAN_EXPORT lean_obj_res leansudo_prim_edit_faccessat(uint32_t dir, b_lean_obj_arg path,
        uint32_t mode) {
    if (faccessat((int)dir, lean_string_cstr(path), (int)mode, 0)) return edit_error(errno);
    return edit_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res leansudo_prim_edit_unlinkat(uint32_t dir, b_lean_obj_arg path) {
    if (unlinkat((int)dir, lean_string_cstr(path), 0)) return edit_error(errno);
    return edit_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res leansudo_prim_edit_fstat(uint32_t fd) {
    struct stat st;
    if (fstat((int)fd, &st)) return edit_error(errno);
    uint64_t values[] = { st.st_mode, st.st_uid, st.st_gid, (uint64_t)st.st_size,
        (uint64_t)st.st_mtim.tv_sec, (uint64_t)st.st_mtim.tv_nsec,
        st.st_nlink, st.st_dev, st.st_ino };
    lean_object *a = lean_mk_empty_array_with_capacity(lean_box(9));
    for (size_t i = 0; i < 9; ++i) a = lean_array_push(a, lean_uint64_to_nat(values[i]));
    return edit_ok(a);
}

LEAN_EXPORT lean_obj_res leansudo_prim_edit_pread(uint32_t fd, uint64_t offset,
        uint32_t count) {
    lean_object *bytes = lean_alloc_sarray(1, 0, count);
    ssize_t n = pread((int)fd, lean_sarray_cptr(bytes), count, (off_t)offset);
    if (n < 0) {
        int error = errno;
        lean_dec(bytes);
        return edit_error(error);
    }
    lean_sarray_set_size(bytes, (size_t)n);
    return edit_ok(bytes);
}

LEAN_EXPORT lean_obj_res leansudo_prim_edit_pwrite(uint32_t fd, b_lean_obj_arg bytes,
        uint64_t offset, uint64_t count) {
    size_t length = lean_sarray_size(bytes);
    uint64_t max_offset = ((uint64_t)1 << (sizeof(off_t) * CHAR_BIT - 1)) - 1;
    if (offset > length || count > length - (size_t)offset ||
        count > (uint64_t)SSIZE_MAX || offset > max_offset)
        return edit_error(EINVAL);
    ssize_t n = pwrite((int)fd, lean_sarray_cptr(bytes) + offset, (size_t)count, (off_t)offset);
    if (n < 0) return edit_error(errno);
    return edit_ok(lean_box_uint64((uint64_t)n));
}

LEAN_EXPORT lean_obj_res leansudo_prim_edit_ftruncate(uint32_t fd, uint64_t size) {
    if (ftruncate((int)fd, (off_t)size)) return edit_error(errno);
    return edit_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res leansudo_prim_edit_fsync(uint32_t fd) {
    if (fsync((int)fd)) return edit_error(errno);
    return edit_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res leansudo_prim_edit_futimens(uint32_t fd, uint64_t seconds,
        uint64_t nanos) {
    struct timespec times[2] = {
        { (time_t)seconds, (long)nanos }, { (time_t)seconds, (long)nanos }
    };
    if (futimens((int)fd, times)) return edit_error(errno);
    return edit_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res leansudo_prim_edit_clock(void) {
    struct timespec ts;
    if (clock_gettime(CLOCK_REALTIME, &ts)) return edit_error(errno);
    lean_object *time = lean_alloc_ctor(0, 0, 16);
    lean_ctor_set_uint64(time, 0, (uint64_t)ts.tv_sec);
    lean_ctor_set_uint64(time, 8, (uint64_t)ts.tv_nsec);
    return edit_ok(time);
}
