/* sudoedit filesystem primitives. Privileged path operations execute only in
 * forked workers with permanently dropped and verified credentials. Directory
 * descriptors pin each checked component; no pathname is re-walked at copyback.
 * Selection, writable-directory refusal and copyback decisions live in Lean. */
#include <lean/lean.h>
#include <errno.h>
#include <fcntl.h>
#include <grp.h>
#include <limits.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/socket.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <unistd.h>

static lean_obj_res error(int e) {
    return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(strerror(e))));
}
static const char *string_arg(b_lean_obj_arg s) {
    const char *p = lean_string_cstr(s);
    return strlen(p) == lean_string_size(s) - 1 ? p : NULL;
}
static int drop(uid_t uid, gid_t gid, gid_t *groups, size_t n, gid_t *verify) {
    uid_t r, e, s;
    gid_t gr, ge, gs;
    if (setgroups(n, groups) || setresgid(gid, gid, gid) || setresuid(uid, uid, uid)) return -1;
    if (getresuid(&r, &e, &s) || getresgid(&gr, &ge, &gs)) return -1;
    if (r != uid || e != uid || s != uid || gr != gid || ge != gid || gs != gid) goto bad;
    if (getgroups((int)n, verify) != (int)n) goto bad;
    /* Linux may sort supplementary groups. Compare membership, not order. */
    for (size_t i = 0; i < n; ++i) {
        size_t j;
        for (j = 0; j < n && verify[i] != groups[j]; ++j) {}
        if (j == n) goto bad;
    }
    if (uid != 0 && setuid(0) != -1) goto bad;
    return 0;
bad:
    errno = EPERM;
    return -1;
}
struct reply { int err; int value; char name[PATH_MAX]; };
/* op: 0 directory, 1 read regular (ENOENT is optional), 2 write regular,
 * 3 W_OK directory, 4 mkstemp, 5 unlink, 6 executable regular (follows links),
 * 7 directory following links, 8 read regular following links, 9 write following links.
 * SCM_RIGHTS transfers opened descriptors, never numeric child-local handles. */
static int worker(uint32_t op, int dir, const char *path, uid_t uid, gid_t gid,
                  b_lean_obj_arg gs, mode_t mask, struct reply *out) {
    size_t n = lean_array_size(gs);
    if (uid == (uid_t)-1 || gid == (gid_t)-1 || n > INT_MAX || mask > 0777) { errno = EINVAL; return -1; }
    gid_t *groups = calloc(n + 1, sizeof(gid_t));
    gid_t *verify = calloc(n + 1, sizeof(gid_t));
    if (!groups || !verify) { free(groups); free(verify); errno = ENOMEM; return -1; }
    for (size_t i = 0; i < n; ++i) {
        groups[i] = lean_unbox_uint32(lean_array_get_core(gs, i));
        if (groups[i] == (gid_t)-1) { free(groups); free(verify); errno = EINVAL; return -1; }
    }
    int sv[2];
    if (socketpair(AF_UNIX, SOCK_SEQPACKET | SOCK_CLOEXEC, 0, sv)) { free(groups); free(verify); return -1; }
    pid_t pid = fork();
    if (pid == -1) { int e = errno; close(sv[0]); close(sv[1]); free(groups); free(verify); errno = e; return -1; }
    if (pid == 0) {
        close(sv[0]);
        struct reply result;
        memset(&result, 0, sizeof result);
        int fd = -1;
        if (drop(uid, gid, groups, n, verify)) result.err = errno;
        else {
            umask(mask);
            switch (op) {
            case 0: case 7:
                fd = openat(dir, path, O_PATH | O_DIRECTORY | O_CLOEXEC | (op == 0 ? O_NOFOLLOW : 0));
                if (fd < 0) result.err = errno;
                break;
            case 1: case 2: case 6: case 8: case 9: {
                int flags = op == 6 ? O_PATH : ((op == 2 || op == 9) ? O_WRONLY | O_CREAT : O_RDONLY);
                if (op == 1 || op == 2) flags |= O_NOFOLLOW;
                fd = openat(dir, path, flags | O_NONBLOCK | O_NOCTTY | O_CLOEXEC, 0644);
                if (fd < 0) {
                    if ((op == 1 || op == 8) && errno == ENOENT) result.value = 1;
                    else result.err = errno;
                } else {
                    struct stat st;
                    if (fstat(fd, &st)) result.err = errno;
                    else if (!S_ISREG(st.st_mode)) result.err = EINVAL;
                    else if (op == 6 && faccessat(dir, path, X_OK, 0)) result.err = errno;
                }
                break;
            }
            case 3:
                if (faccessat(dir, ".", W_OK, 0) == 0) result.value = 1;
                else if (errno != EACCES && errno != EROFS) result.err = errno;
                break;
            case 4:
                if (strlen(path) >= sizeof result.name) result.err = ENAMETOOLONG;
                else {
                    strcpy(result.name, path);
                    fd = mkostemp(result.name, O_CLOEXEC);
                    if (fd < 0) result.err = errno;
                }
                break;
            case 5:
                if (unlinkat(dir, path, 0) && errno != ENOENT) result.err = errno;
                break;
            default: result.err = EINVAL;
            }
        }
        struct iovec io = { &result, sizeof result };
        char control[CMSG_SPACE(sizeof(int))];
        memset(control, 0, sizeof control);
        struct msghdr msg;
        memset(&msg, 0, sizeof msg);
        msg.msg_iov = &io; msg.msg_iovlen = 1;
        if (fd >= 0 && result.err == 0) {
            msg.msg_control = control; msg.msg_controllen = sizeof control;
            struct cmsghdr *c = CMSG_FIRSTHDR(&msg);
            c->cmsg_level = SOL_SOCKET; c->cmsg_type = SCM_RIGHTS; c->cmsg_len = CMSG_LEN(sizeof(int));
            memcpy(CMSG_DATA(c), &fd, sizeof fd);
        }
        ssize_t sent;
        do { sent = sendmsg(sv[1], &msg, MSG_NOSIGNAL); } while (sent < 0 && errno == EINTR);
        if (op == 4 && fd >= 0 && sent != (ssize_t)sizeof result) {
            int ignored = unlink(result.name); (void)ignored;
        }
        _exit(sent == (ssize_t)sizeof result ? 0 : 1);
    }
    close(sv[1]); free(groups); free(verify);
    struct iovec io = { out, sizeof *out };
    char control[CMSG_SPACE(sizeof(int))];
    struct msghdr msg;
    memset(&msg, 0, sizeof msg); memset(control, 0, sizeof control);
    msg.msg_iov = &io; msg.msg_iovlen = 1;
    msg.msg_control = control; msg.msg_controllen = sizeof control;
    ssize_t got;
    do { got = recvmsg(sv[0], &msg, MSG_CMSG_CLOEXEC); } while (got < 0 && errno == EINTR);
    int fd = -1;
    struct cmsghdr *c = CMSG_FIRSTHDR(&msg);
    if (c && c->cmsg_level == SOL_SOCKET && c->cmsg_type == SCM_RIGHTS && c->cmsg_len == CMSG_LEN(sizeof(int)))
        memcpy(&fd, CMSG_DATA(c), sizeof fd);
    close(sv[0]);
    int status = 0; pid_t waited;
    do { waited = waitpid(pid, &status, 0); } while (waited < 0 && errno == EINTR);
    if (got != (ssize_t)sizeof *out || (msg.msg_flags & (MSG_TRUNC | MSG_CTRUNC)) || waited != pid || !WIFEXITED(status) || WEXITSTATUS(status)) {
        if (fd >= 0) close(fd);
        errno = EIO; return -1;
    }
    if (out->err) { if (fd >= 0) close(fd); errno = out->err; return -1; }
    errno = 0;
    return fd;
}
LEAN_EXPORT lean_obj_res leansudo_edit_op(uint32_t op, uint32_t dir, b_lean_obj_arg path,
        uint32_t uid, uint32_t gid, b_lean_obj_arg groups, uint32_t mask) {
    const char *p = string_arg(path);
    if (!p || (dir != UINT32_MAX && dir > INT_MAX)) return error(EINVAL);
    struct reply r;
    memset(&r, 0, sizeof r);
    errno = 0;
    int fd = worker(op, dir == UINT32_MAX ? AT_FDCWD : (int)dir, p, uid, gid, groups, mask, &r);
    if (fd < 0 && errno) return error(errno);
    lean_object *result = lean_alloc_ctor(0, 1, 4);
    lean_ctor_set(result, 0, lean_mk_string(r.name));
    lean_ctor_set_uint32(result, sizeof(void *), op == 3 ? (uint32_t)r.value : (fd < 0 ? UINT32_MAX : (uint32_t)fd));
    return lean_io_result_mk_ok(result);
}
LEAN_EXPORT lean_obj_res leansudo_edit_close(uint32_t fd) {
    if (fd <= INT_MAX) close((int)fd);
    return lean_io_result_mk_ok(lean_box(0));
}
LEAN_EXPORT lean_obj_res leansudo_edit_stat(uint32_t fd) {
    struct stat st;
    if (fd > INT_MAX || fstat((int)fd, &st)) return error(errno ? errno : EBADF);
    uint64_t values[] = { st.st_mode, st.st_uid, st.st_gid, (uint64_t)st.st_size,
        (uint64_t)st.st_mtim.tv_sec, (uint64_t)st.st_mtim.tv_nsec, st.st_nlink, st.st_dev, st.st_ino };
    lean_object *a = lean_mk_empty_array();
    for (size_t i = 0; i < sizeof values / sizeof values[0]; ++i) a = lean_array_push(a, lean_uint64_to_nat(values[i]));
    return lean_io_result_mk_ok(a);
}
LEAN_EXPORT lean_obj_res leansudo_edit_read(uint32_t fd) {
    struct stat st;
    if (fd > INT_MAX || fstat((int)fd, &st)) return error(errno ? errno : EBADF);
    if (!S_ISREG(st.st_mode) || st.st_size < 0 || (uintmax_t)st.st_size > SIZE_MAX) return error(EINVAL);
    size_t size = (size_t)st.st_size;
    lean_object *a = lean_alloc_sarray(1, size, size);
    size_t pos = 0;
    while (pos < size) {
        ssize_t n = pread((int)fd, lean_sarray_cptr(a) + pos, size - pos, (off_t)pos);
        if (n < 0 && errno == EINTR) continue;
        if (n <= 0) { int e = n == 0 ? EIO : errno; lean_dec(a); return error(e); }
        pos += (size_t)n;
    }
    struct stat after;
    if (fstat((int)fd, &after) || after.st_size != st.st_size || after.st_mtim.tv_sec != st.st_mtim.tv_sec || after.st_mtim.tv_nsec != st.st_mtim.tv_nsec) {
        lean_dec(a); return error(EAGAIN);
    }
    return lean_io_result_mk_ok(a);
}
static int replace_bytes(int fd, b_lean_obj_arg bytes) {
    size_t size = lean_sarray_size(bytes), pos = 0;
    while (pos < size) {
        ssize_t n = pwrite(fd, lean_sarray_cptr(bytes) + pos, size - pos, (off_t)pos);
        if (n < 0 && errno == EINTR) continue;
        if (n <= 0) { if (n == 0) errno = EIO; return -1; }
        pos += (size_t)n;
    }
    if (ftruncate(fd, (off_t)size) || fsync(fd)) return -1;
    return 0;
}
/* Write without truncating first. On failure restore the caller's original
 * snapshot; the editable temporary copy is retained by Lean in either case. */
LEAN_EXPORT lean_obj_res leansudo_edit_write(uint32_t fd, b_lean_obj_arg bytes, b_lean_obj_arg original) {
    if (fd > INT_MAX) return error(EBADF);
    if (replace_bytes((int)fd, bytes)) {
        int e = errno;
        if (replace_bytes((int)fd, original))
            return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string("write failed and original contents could not be restored")));
        return error(e);
    }
    return lean_io_result_mk_ok(lean_box(0));
}
