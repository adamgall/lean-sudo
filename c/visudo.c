/*
 * lean-sudo C shim for visudo (LeanSudo.Visudo.Sys): locking the sudoers file,
 * exclusive creation of the temporary copy, and fixing its owner/mode before it is
 * renamed over the original.
 *
 * Conventions as in core.c: IO functions return a Lean IO result (no world
 * argument), string arguments are borrowed and rejected if they contain NUL.
 */
#include <lean/lean.h>

#include <errno.h>
#include <fcntl.h>
#include <stdarg.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <unistd.h>

static lean_obj_res io_err(const char *msg) {
    return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(msg)));
}

static lean_obj_res io_errno_path(const char *what, const char *path, int e) {
    char ebuf[256], buf[1024];
    snprintf(buf, sizeof buf, "%s %s: %s", what, path, strerror_r(e, ebuf, sizeof ebuf));
    return io_err(buf);
}

static const char *cstr_arg(b_lean_obj_arg s) {
    const char *c = lean_string_cstr(s);
    if (strlen(c) != lean_string_size(s) - 1) return NULL;
    return c;
}

/* The lock descriptor; kept open (close-on-exec) until the process exits. */
static int lock_fd = -1;

/*
 * Write-lock `path` with an open-file-description lock (F_OFD_SETLK). OFD locks
 * conflict with the classic fcntl(F_SETLK) lock sudo.ws's visudo takes on the same
 * file, but unlike those they are not dropped when this process closes some other
 * descriptor of the file. Returns 0 = locked, 1 = busy (held elsewhere),
 * 2 = the file does not exist. Symlinks are refused (ELOOP), as sudo refuses them.
 */
LEAN_EXPORT lean_obj_res leansudo_visudo_lock(b_lean_obj_arg path) {
    const char *p = cstr_arg(path);
    if (!p) return io_err("invalid path");
    if (lock_fd != -1) return io_err("sudoers file already locked");
    int fd = open(p, O_RDWR | O_NOFOLLOW | O_NONBLOCK | O_NOCTTY | O_CLOEXEC);
    if (fd < 0) {
        if (errno == ENOENT) return lean_io_result_mk_ok(lean_box(2));
        return io_errno_path("unable to open", p, errno);
    }
    struct flock fl;
    memset(&fl, 0, sizeof fl);
    fl.l_type = F_WRLCK;
    fl.l_whence = SEEK_SET;
    if (fcntl(fd, F_OFD_SETLK, &fl) != 0) {
        int e = errno;
        close(fd);
        if (e == EAGAIN || e == EACCES) return lean_io_result_mk_ok(lean_box(1));
        return io_errno_path("unable to lock", p, e);
    }
    lock_fd = fd;
    return lean_io_result_mk_ok(lean_box(0));
}

/*
 * Create `path` with O_CREAT|O_EXCL (never follows or reuses an existing file or
 * symlink), mode 0600, write `content` completely and fsync it.
 * Returns false if the file already exists.
 */
LEAN_EXPORT lean_obj_res leansudo_visudo_create_excl(b_lean_obj_arg path, b_lean_obj_arg content) {
    const char *p = cstr_arg(path);
    if (!p) return io_err("invalid path");
    int fd = open(p, O_WRONLY | O_CREAT | O_EXCL | O_NOFOLLOW | O_NOCTTY | O_CLOEXEC, 0600);
    if (fd < 0) {
        if (errno == EEXIST) return lean_io_result_mk_ok(lean_box(0));
        return io_errno_path("unable to create", p, errno);
    }
    const char *buf = lean_string_cstr(content);
    size_t left = lean_string_size(content) - 1;
    while (left > 0) {
        ssize_t n = write(fd, buf, left);
        if (n < 0) {
            if (errno == EINTR) continue;
            int e = errno;
            close(fd);
            unlink(p);
            return io_errno_path("unable to write to", p, e);
        }
        buf += n;
        left -= (size_t)n;
    }
    if (fsync(fd) != 0 || close(fd) != 0) {
        int e = errno;
        unlink(p);
        return io_errno_path("unable to write to", p, e);
    }
    return lean_io_result_mk_ok(lean_box(1));
}

/*
 * Open `path` without following symlinks, require a regular file, then
 * fchown(uid, gid), fchmod(mode) and fsync it.
 */
LEAN_EXPORT lean_obj_res leansudo_visudo_set_owner_mode(b_lean_obj_arg path, uint32_t uid,
                                                        uint32_t gid, uint32_t mode) {
    const char *p = cstr_arg(path);
    if (!p) return io_err("invalid path");
    if (uid == (uint32_t)-1 || gid == (uint32_t)-1 || (mode & ~07777u) != 0)
        return io_err("invalid owner or mode");
    int fd = open(p, O_RDONLY | O_NOFOLLOW | O_NONBLOCK | O_NOCTTY | O_CLOEXEC);
    if (fd < 0) return io_errno_path("unable to open", p, errno);
    struct stat st;
    if (fstat(fd, &st) != 0) {
        int e = errno;
        close(fd);
        return io_errno_path("unable to stat", p, e);
    }
    if (!S_ISREG(st.st_mode)) {
        close(fd);
        char buf[1024];
        snprintf(buf, sizeof buf, "%s is not a regular file", p);
        return io_err(buf);
    }
    if (fchown(fd, (uid_t)uid, (gid_t)gid) != 0) {
        int e = errno;
        close(fd);
        return io_errno_path("unable to set (uid, gid) of", p, e);
    }
    if (fchmod(fd, (mode_t)mode) != 0) {
        int e = errno;
        close(fd);
        return io_errno_path("unable to change mode of", p, e);
    }
    if (fsync(fd) != 0) {
        int e = errno;
        close(fd);
        return io_errno_path("unable to sync", p, e);
    }
    close(fd);
    return lean_io_result_mk_ok(lean_box(0));
}
