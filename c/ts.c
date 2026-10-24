/*
 * Timestamp storage shim for LeanSudo.Sys.Timestamp: boot clock, process identity,
 * and the locked per-user timestamp file. No policy lives here.
 */
#include <lean/lean.h>

#include <errno.h>
#include <fcntl.h>
#include <stdarg.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/file.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <time.h>
#include <unistd.h>

/* Maximum timestamp file size we are willing to read. */
#define TS_READ_CAP (64 * 1024)

/*
 * Bounded formatting; messages are silently truncated (they only contain paths of
 * bounded length and errno text).
 */
__attribute__((format(printf, 3, 4)))
static void ts_fmt(char *buf, size_t len, const char *fmt, ...) {
    va_list ap;
    va_start(ap, fmt);
    vsnprintf(buf, len, fmt, ap);
    va_end(ap);
}

static lean_obj_res ts_user_error(const char *msg) {
    return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(msg)));
}

static lean_obj_res ts_errno_error(const char *what, int err) {
    char buf[4608];
    ts_fmt(buf, sizeof buf, "%s: %s", what, strerror(err));
    return ts_user_error(buf);
}

/* ---- clocks and process identity ---------------------------------------- */

LEAN_EXPORT lean_obj_res lean_sudo_ts_boottime(lean_obj_arg w) {
    (void)w;
    struct timespec ts;
    if (clock_gettime(CLOCK_BOOTTIME, &ts) != 0)
        return ts_errno_error("clock_gettime(CLOCK_BOOTTIME)", errno);
    uint64_t ns = (uint64_t)ts.tv_sec * UINT64_C(1000000000) + (uint64_t)ts.tv_nsec;
    return lean_io_result_mk_ok(lean_uint64_to_nat(ns));
}

LEAN_EXPORT lean_obj_res lean_sudo_ts_getsid(lean_obj_arg w) {
    (void)w;
    pid_t sid = getsid(0);
    if (sid < 0)
        return ts_errno_error("getsid", errno);
    return lean_io_result_mk_ok(lean_box_uint32((uint32_t)sid));
}

LEAN_EXPORT lean_obj_res lean_sudo_ts_getppid(lean_obj_arg w) {
    (void)w;
    return lean_io_result_mk_ok(lean_box_uint32((uint32_t)getppid()));
}

/* ---- timestamp file ------------------------------------------------------ */

/*
 * Open (creating if `create`) the directory `name` relative to `dirfd` without
 * following symlinks, and verify the *opened* directory: a directory owned by
 * uid 0 that is not group/world writable. A freshly created directory gets
 * exactly `mode` (independent of the umask). Returns the fd or -1 with `err` set.
 */
static int ts_open_dir(int dirfd, const char *name, const char *display, mode_t mode,
                       bool create, char *err, size_t errlen) {
    bool created = false;
    if (create) {
        if (mkdirat(dirfd, name, mode) == 0) {
            created = true;
        } else if (errno != EEXIST) {
            ts_fmt(err, errlen, "%s: %s", display, strerror(errno));
            return -1;
        }
    }
    int fd = openat(dirfd, name, O_RDONLY | O_DIRECTORY | O_NOFOLLOW | O_CLOEXEC);
    if (fd < 0) {
        int e = errno;
        if (e == ELOOP || e == ENOTDIR)
            ts_fmt(err, errlen, "%s: not a directory", display);
        else
            ts_fmt(err, errlen, "%s: %s", display, strerror(e));
        errno = e;
        return -1;
    }
    struct stat st;
    if (fstat(fd, &st) != 0) {
        int e = errno;
        ts_fmt(err, errlen, "%s: %s", display, strerror(e));
        close(fd);
        errno = e;
        return -1;
    }
    if (!S_ISDIR(st.st_mode)) {
        ts_fmt(err, errlen, "%s: not a directory", display);
        close(fd);
        errno = ENOTDIR;
        return -1;
    }
    if (st.st_uid != 0) {
        ts_fmt(err, errlen, "%s is owned by uid %u, should be 0", display,
                 (unsigned)st.st_uid);
        close(fd);
        errno = EPERM;
        return -1;
    }
    if (created && fchmod(fd, mode) != 0) {
        int e = errno;
        ts_fmt(err, errlen, "%s: %s", display, strerror(e));
        close(fd);
        errno = e;
        return -1;
    }
    if (!created && (st.st_mode & (S_IWGRP | S_IWOTH)) != 0) {
        ts_fmt(err, errlen, "%s is group or world writable", display);
        close(fd);
        errno = EPERM;
        return -1;
    }
    return fd;
}

/* Persistent per-user marker, separate from authentication timestamps. */
LEAN_EXPORT lean_obj_res lean_sudo_state_marker(b_lean_obj_arg path, uint32_t uid,
        uint8_t create, lean_obj_arg w) {
    (void)w;
    const char *p = lean_string_cstr(path);
    if (strlen(p) != lean_string_size(path) - 1 || p[0] != '/')
        return ts_user_error("invalid state directory");
    char *copy = strdup(p);
    if (!copy) return ts_errno_error("state directory", ENOMEM);
    int dir = open("/", O_RDONLY | O_DIRECTORY | O_CLOEXEC);
    if (dir < 0) { free(copy); return ts_errno_error("/", errno); }
    char err[4608], *save = NULL;
    for (char *name = strtok_r(copy, "/", &save); name; name = strtok_r(NULL, "/", &save)) {
        if (!strcmp(name, ".") || !strcmp(name, "..")) {
            close(dir); free(copy); return ts_user_error("invalid state directory component");
        }
        int next = ts_open_dir(dir, name, p, 0700, create, err, sizeof(err));
        close(dir);
        if (next < 0) {
            free(copy);
            if (!create && errno == ENOENT) return lean_io_result_mk_ok(lean_box(0));
            return ts_user_error(err);
        }
        dir = next;
    }
    free(copy);
    char name[16];
    ts_fmt(name, sizeof(name), "%u", (unsigned)uid);
    int fd = openat(dir, name, O_RDONLY | O_NOFOLLOW | O_CLOEXEC | O_NONBLOCK |
        (create ? O_CREAT : 0), 0600);
    int saved = errno;
    close(dir);
    if (fd < 0) {
        if (!create && saved == ENOENT) return lean_io_result_mk_ok(lean_box(0));
        return ts_errno_error("state marker", saved);
    }
    struct stat st;
    bool valid = fstat(fd, &st) == 0 && S_ISREG(st.st_mode) &&
        st.st_uid == 0 && !(st.st_mode & 022);
    close(fd);
    if (!valid) return ts_user_error("unsafe state marker");
    return lean_io_result_mk_ok(lean_box(1));
}

/* Open and verify `<base>` and `<base>/ts`. Returns the ts dir fd or -1. */
static int ts_open_tsdir(const char *base, bool create, char *err, size_t errlen) {
    if (geteuid() != 0) {
        ts_fmt(err, errlen, "timestamp storage requires effective uid 0");
        errno = EPERM;
        return -1;
    }
    if (base[0] != '/') {
        ts_fmt(err, errlen, "%s: timestamp directory must be an absolute path", base);
        errno = EINVAL;
        return -1;
    }
    int bfd = ts_open_dir(AT_FDCWD, base, base, 0711, create, err, errlen);
    if (bfd < 0)
        return -1;
    char display[4096];
    ts_fmt(display, sizeof display, "%s/ts", base);
    int tfd = ts_open_dir(bfd, "ts", display, 0700, create, err, errlen);
    int e = errno;
    close(bfd);
    errno = e;
    return tfd;
}

/* Open, verify and exclusively lock `<base>/ts/<uid>`; returns the fd. */
LEAN_EXPORT lean_obj_res lean_sudo_ts_open(b_lean_obj_arg base, uint32_t uid, lean_obj_arg w) {
    (void)w;
    char err[4608];
    const char *b = lean_string_cstr(base);
    int tfd = ts_open_tsdir(b, true, err, sizeof err);
    if (tfd < 0)
        return ts_user_error(err);
    char name[16];
    ts_fmt(name, sizeof name, "%u", (unsigned)uid);
    char display[4608];
    ts_fmt(display, sizeof display, "%s/ts/%s", b, name);
    int fd = openat(tfd, name, O_RDWR | O_CREAT | O_NOFOLLOW | O_CLOEXEC | O_NOCTTY, 0600);
    int e = errno;
    close(tfd);
    if (fd < 0)
        return ts_errno_error(display, e);
    struct stat st;
    if (fstat(fd, &st) != 0) {
        e = errno;
        close(fd);
        return ts_errno_error(display, e);
    }
    const char *bad = NULL;
    if (!S_ISREG(st.st_mode))
        bad = "not a regular file";
    else if (st.st_uid != 0)
        bad = "not owned by uid 0";
    else if (st.st_nlink != 1)
        bad = "has more than one link";
    else if ((st.st_mode & 077) != 0)
        bad = "is accessible by group or other";
    if (bad != NULL) {
        close(fd);
        ts_fmt(err, sizeof err, "%s: %s", display, bad);
        return ts_user_error(err);
    }
    while (flock(fd, LOCK_EX) != 0) {
        if (errno != EINTR) {
            e = errno;
            close(fd);
            return ts_errno_error(display, e);
        }
    }
    return lean_io_result_mk_ok(lean_box_uint32((uint32_t)fd));
}

/* Read the whole file from offset 0. Files larger than TS_READ_CAP read as empty. */
LEAN_EXPORT lean_obj_res lean_sudo_ts_read(uint32_t fd, lean_obj_arg w) {
    (void)w;
    const size_t bufsize = TS_READ_CAP + 1;
    unsigned char *buf = malloc(bufsize);
    if (buf == NULL)
        return ts_errno_error("timestamp read", ENOMEM);
    size_t total = 0;
    while (total < bufsize) {
        ssize_t n = pread((int)fd, buf + total, bufsize - total, (off_t)total);
        if (n < 0) {
            if (errno == EINTR)
                continue;
            int e = errno;
            free(buf);
            return ts_errno_error("timestamp read", e);
        }
        if (n == 0)
            break;
        total += (size_t)n;
    }
    if (total > TS_READ_CAP)
        total = 0;
    lean_object *arr = lean_alloc_sarray(1, total, total);
    if (total > 0)
        memcpy(lean_sarray_cptr(arr), buf, total);
    free(buf);
    return lean_io_result_mk_ok(arr);
}

/* Replace the file contents with `bytes` and fsync. */
LEAN_EXPORT lean_obj_res lean_sudo_ts_write(uint32_t fd, b_lean_obj_arg bytes, lean_obj_arg w) {
    (void)w;
    size_t len = lean_sarray_size(bytes);
    const uint8_t *p = lean_sarray_cptr(bytes);
    if (len > TS_READ_CAP)
        return ts_user_error("timestamp write: record data too large");
    if (ftruncate((int)fd, 0) != 0)
        return ts_errno_error("timestamp ftruncate", errno);
    size_t off = 0;
    while (off < len) {
        ssize_t n = pwrite((int)fd, p + off, len - off, (off_t)off);
        if (n < 0) {
            if (errno == EINTR)
                continue;
            return ts_errno_error("timestamp write", errno);
        }
        off += (size_t)n;
    }
    if (fsync((int)fd) != 0)
        return ts_errno_error("timestamp fsync", errno);
    return lean_io_result_mk_ok(lean_box(0));
}

/* Close (and thereby unlock) the timestamp file. */
LEAN_EXPORT lean_obj_res lean_sudo_ts_close(uint32_t fd, lean_obj_arg w) {
    (void)w;
    close((int)fd);
    return lean_io_result_mk_ok(lean_box(0));
}

/* Unlink `<base>/ts/<uid>` (sudo -K). A missing directory or file is not an error. */
LEAN_EXPORT lean_obj_res lean_sudo_ts_remove(b_lean_obj_arg base, uint32_t uid, lean_obj_arg w) {
    (void)w;
    char err[4608];
    const char *b = lean_string_cstr(base);
    int tfd = ts_open_tsdir(b, false, err, sizeof err);
    if (tfd < 0) {
        if (errno == ENOENT)
            return lean_io_result_mk_ok(lean_box(0));
        return ts_user_error(err);
    }
    char name[16];
    ts_fmt(name, sizeof name, "%u", (unsigned)uid);
    int r = unlinkat(tfd, name, 0);
    int e = errno;
    close(tfd);
    if (r != 0 && e != ENOENT) {
        char display[4608];
        ts_fmt(display, sizeof display, "%s/ts/%s", b, name);
        return ts_errno_error(display, e);
    }
    return lean_io_result_mk_ok(lean_box(0));
}
