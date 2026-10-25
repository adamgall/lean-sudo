#include "shim.h"

#include <errno.h>
#include <fcntl.h>
#include <limits.h>
#include <pthread.h>
#include <signal.h>
#include <stdatomic.h>
#include <stdarg.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <sys/time.h>
#include <time.h>
#include <unistd.h>

static lean_obj_res ts_errno_error(const char *what, int err) {
    char buf[4608];
    snprintf(buf, sizeof buf, "%s: %s", what, strerror(err));
    return ls_error(buf);
}

static int ts_real_time(struct timespec *ts) {
    int rc = TEMP_FAILURE_RETRY(clock_gettime(CLOCK_REALTIME, ts));
    if (rc != 0) {
        struct timeval tv;
        rc = TEMP_FAILURE_RETRY(gettimeofday(&tv, NULL));
        if (rc == 0) {
            ts->tv_sec = tv.tv_sec;
            ts->tv_nsec = tv.tv_usec * 1000L;
        }
    }
    return rc;
}

LEAN_EXPORT lean_obj_res lean_sudo_ts_boottime(lean_obj_arg w) {
    (void)w;
    struct timespec ts;
    static bool use_real_time;
    if (sysconf(_SC_MONOTONIC_CLOCK) == -1) use_real_time = true;
    int rc = use_real_time ? -1 : TEMP_FAILURE_RETRY(clock_gettime(CLOCK_BOOTTIME, &ts));
    if (rc != 0) {
        use_real_time = true;
        rc = ts_real_time(&ts);
    }
    if (rc != 0)
        return ts_errno_error("timestamp clock", errno);
    if (ts.tv_sec < 0 || ts.tv_nsec < 0 || ts.tv_nsec >= 1000000000L ||
            (uint64_t)ts.tv_sec > (UINT64_MAX - (uint64_t)ts.tv_nsec) / UINT64_C(1000000000))
        return ts_errno_error("timestamp clock", EOVERFLOW);
    uint64_t ns = (uint64_t)ts.tv_sec * UINT64_C(1000000000) + (uint64_t)ts.tv_nsec;
    return lean_io_result_mk_ok(lean_uint64_to_nat(ns));
}

LEAN_EXPORT lean_obj_res lean_sudo_ts_clock_ticks(lean_obj_arg w) {
    (void)w;
    errno = 0;
    long ticks = sysconf(_SC_CLK_TCK);
    if (ticks <= 0)
        return ts_errno_error("sysconf(_SC_CLK_TCK)", errno ? errno : EINVAL);
    return lean_io_result_mk_ok(lean_uint64_to_nat((uint64_t)ticks));
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

static int ts_open_dir(int dirfd, const char *name, const char *display, mode_t mode,
                       bool create, char *err, size_t errlen) {
    bool created = false;
    if (create) {
        if (mkdirat(dirfd, name, mode) == 0) {
            created = true;
        } else if (errno != EEXIST) {
            snprintf(err, errlen, "%s: %s", display, strerror(errno));
            return -1;
        }
    }
    int fd = openat(dirfd, name, O_RDONLY | O_DIRECTORY | O_NOFOLLOW | O_CLOEXEC);
    if (fd < 0) {
        int e = errno;
        if (e == ELOOP || e == ENOTDIR)
            snprintf(err, errlen, "%s: not a directory", display);
        else
            snprintf(err, errlen, "%s: %s", display, strerror(e));
        errno = e;
        return -1;
    }
    struct stat st;
    if (fstat(fd, &st) != 0) {
        int e = errno;
        snprintf(err, errlen, "%s: %s", display, strerror(e));
        close(fd);
        errno = e;
        return -1;
    }
    if (!S_ISDIR(st.st_mode)) {
        snprintf(err, errlen, "%s: not a directory", display);
        close(fd);
        errno = ENOTDIR;
        return -1;
    }
    if (st.st_uid != 0) {
        snprintf(err, errlen, "%s is owned by uid %u, should be 0", display,
                 (unsigned)st.st_uid);
        close(fd);
        errno = EPERM;
        return -1;
    }
    if (created && fchmod(fd, mode) != 0) {
        int e = errno;
        snprintf(err, errlen, "%s: %s", display, strerror(e));
        close(fd);
        errno = e;
        return -1;
    }
    if (!created && (st.st_mode & (S_IWGRP | S_IWOTH)) != 0) {
        snprintf(err, errlen, "%s is group or world writable", display);
        close(fd);
        errno = EPERM;
        return -1;
    }
    return fd;
}

LEAN_EXPORT lean_obj_res lean_sudo_state_marker(b_lean_obj_arg path, uint32_t uid,
        uint8_t create, lean_obj_arg w) {
    (void)w;
    const char *p = lean_string_cstr(path);
    if (strlen(p) != lean_string_size(path) - 1 || p[0] != '/')
        return ls_error("invalid state directory");
    char *copy = strdup(p);
    if (!copy) return ts_errno_error("state directory", ENOMEM);
    int dir = open("/", O_RDONLY | O_DIRECTORY | O_CLOEXEC);
    if (dir < 0) { free(copy); return ts_errno_error("/", errno); }
    char err[4608], *save = NULL;
    for (char *name = strtok_r(copy, "/", &save); name; name = strtok_r(NULL, "/", &save)) {
        if (!strcmp(name, ".") || !strcmp(name, "..")) {
            close(dir); free(copy); return ls_error("invalid state directory component");
        }
        int next = ts_open_dir(dir, name, p, 0700, create, err, sizeof(err));
        close(dir);
        if (next < 0) {
            free(copy);
            if (!create && errno == ENOENT) return lean_io_result_mk_ok(lean_box(0));
            return ls_error(err);
        }
        dir = next;
    }
    free(copy);
    char name[16];
    snprintf(name, sizeof(name), "%u", (unsigned)uid);
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
    if (!valid) return ls_error("unsafe state marker");
    return lean_io_result_mk_ok(lean_box(1));
}

static int ts_close_error(int fd, int error) {
    if (fd >= 0)
        (void)close(fd);
    errno = error;
    return -1;
}

static bool ts_valid_args(b_lean_obj_arg directory, b_lean_obj_arg filename,
        uint32_t uid, uint32_t gid) {
    const char *path = lean_string_cstr(directory);
    const char *name = lean_string_cstr(filename);
    size_t pathlen = lean_string_size(directory) - 1;
    size_t namelen = lean_string_size(filename) - 1;
    if (uid == UINT32_MAX || gid == UINT32_MAX ||
            (uint64_t)(uid_t)uid != uid || (uint64_t)(gid_t)gid != gid ||
            pathlen == 0 || pathlen >= PATH_MAX || path[0] != '/' ||
            strlen(path) != pathlen || namelen == 0 || namelen > NAME_MAX ||
            strlen(name) != namelen || strchr(name, '/') != NULL ||
            !strcmp(name, ".") || !strcmp(name, ".."))
        return false;
    const char *p = path;
    while (*p) {
        while (*p == '/') p++;
        const char *start = p;
        while (*p && *p != '/') p++;
        size_t len = (size_t)(p - start);
        if (len > NAME_MAX || (len == 1 && start[0] == '.') ||
                (len == 2 && start[0] == '.' && start[1] == '.'))
            return false;
    }
    return true;
}

static int ts_check_directory(int fd, uid_t uid, gid_t gid) {
    struct stat st;
    if (TEMP_FAILURE_RETRY(fstat(fd, &st)) != 0)
        return ts_close_error(fd, errno);
    if (!S_ISDIR(st.st_mode))
        return ts_close_error(fd, ENOTDIR);
    if (st.st_uid != uid || (st.st_mode & S_IWOTH) ||
            ((st.st_mode & S_IWGRP) && st.st_gid != gid))
        return ts_close_error(fd, EACCES);
    return fd;
}

static int ts_directory(const char *path, uid_t uid, gid_t gid, bool create) {
    int dir = TEMP_FAILURE_RETRY(openat(AT_FDCWD, path,
        O_RDONLY | O_DIRECTORY | O_CLOEXEC | O_NONBLOCK, 0));
    if (dir >= 0)
        return ts_check_directory(dir, uid, gid);
    if (!create || errno != ENOENT)
        return -1;

    char copy[PATH_MAX];
    memcpy(copy, path, strlen(path) + 1);
    dir = TEMP_FAILURE_RETRY(openat(AT_FDCWD, "/", O_RDONLY | O_DIRECTORY | O_CLOEXEC, 0));
    if (dir < 0)
        return -1;
    char *save = NULL;
    char *name = strtok_r(copy, "/", &save);
    while (name != NULL) {
        char *next = strtok_r(NULL, "/", &save);
        bool final = next == NULL;
        bool created = false;
        int fd = TEMP_FAILURE_RETRY(openat(dir, name,
            O_RDONLY | O_DIRECTORY | O_CLOEXEC | O_NONBLOCK, 0));
        if (fd < 0 && errno == ENOENT) {
            int rc;
            rc = TEMP_FAILURE_RETRY(mkdirat(dir, name, 0700));
            if (rc == 0)
                created = true;
            else if (errno != EEXIST)
                return ts_close_error(dir, errno);
            fd = TEMP_FAILURE_RETRY(openat(dir, name, O_RDONLY | O_DIRECTORY | O_CLOEXEC |
                O_NONBLOCK | (created && !final ? O_NOFOLLOW : 0), 0));
        }
        if (fd < 0)
            return ts_close_error(dir, errno);
        (void)close(dir);
        dir = fd;
        struct stat st;
        if (TEMP_FAILURE_RETRY(fstat(dir, &st)) != 0)
            return ts_close_error(dir, errno);
        if (!S_ISDIR(st.st_mode))
            return ts_close_error(dir, ENOTDIR);
        if (created || final) {
            int rc;
            rc = TEMP_FAILURE_RETRY(fchown(dir, uid, gid));
            if (rc != 0)
                return ts_close_error(dir, errno);
            if (created) {
                rc = TEMP_FAILURE_RETRY(fchmod(dir, final ? 0700 : 0711));
                if (rc != 0)
                    return ts_close_error(dir, errno);
            }
        }
        name = next;
    }
    return ts_check_directory(dir, uid, gid);
}

static int ts_owner_open(int dir, const char *name, uid_t uid, bool create) {
    uid_t saved = geteuid();
    int rc;
    if (saved != uid) {
        rc = TEMP_FAILURE_RETRY(seteuid(uid));
        if (rc != 0)
            return -1;
    }
    int fd = TEMP_FAILURE_RETRY(openat(dir, name, O_RDWR | O_CLOEXEC |
        (create ? O_CREAT : 0), 0600));
    int error = errno;
    if (saved != uid) {
        rc = TEMP_FAILURE_RETRY(seteuid(saved));
        if (rc != 0)
            return ts_close_error(fd, errno);
    }
    errno = error;
    return fd;
}

static bool ts_boot_epoch(struct timespec *boot) {
    int fd = TEMP_FAILURE_RETRY(openat(AT_FDCWD, "/proc/stat", O_RDONLY | O_CLOEXEC, 0));
    if (fd < 0)
        return false;
    FILE *fp = fdopen(fd, "r");
    if (fp == NULL) {
        (void)close(fd);
        return false;
    }
    char line[256];
    bool found = false, line_start = true;
    for (;;) {
        errno = 0;
        if (fgets(line, sizeof(line), fp) == NULL) {
            if (ferror(fp) && errno == EINTR) {
                clearerr(fp);
                continue;
            }
            break;
        }
        bool complete = strchr(line, '\n') != NULL;
        if (line_start && complete && !strncmp(line, "btime ", 6)) {
            const char *end = line + 6;
            long long value = 0;
            while (*end >= '0' && *end <= '9') {
                int digit = *end - '0';
                if (value > (LLONG_MAX - digit) / 10)
                    break;
                value = value * 10 + digit;
                end++;
            }
            if (value > 0 && end != line + 6 &&
                    *end == '\n' && end[1] == '\0' &&
                    (long long)(time_t)value == value) {
                boot->tv_sec = (time_t)value;
                boot->tv_nsec = 0;
                found = true;
                break;
            }
        }
        line_start = complete;
    }
    (void)fclose(fp);
    return found;
}

static bool ts_predates_boot(const struct stat *st) {
    struct timespec now, boot;
    if (ts_real_time(&now) != 0 || !ts_boot_epoch(&boot))
        return false;
    if (now.tv_sec < boot.tv_sec ||
            (now.tv_sec == boot.tv_sec && now.tv_nsec < boot.tv_nsec))
        return false;
    return st->st_mtime < boot.tv_sec;
}

LEAN_EXPORT lean_obj_res lean_sudo_ts_open(b_lean_obj_arg directory,
        b_lean_obj_arg filename, uint32_t owner_uid, uint32_t owner_gid,
        uint8_t create, lean_obj_arg w) {
    (void)w;
    if (!ts_valid_args(directory, filename, owner_uid, owner_gid))
        return ts_errno_error("timestamp path or owner", EINVAL);
    const char *name = lean_string_cstr(filename);
    int dir = ts_directory(lean_string_cstr(directory), (uid_t)owner_uid,
        (gid_t)owner_gid, create != 0);
    if (dir < 0) {
        if (!create && errno == ENOENT)
            return lean_io_result_mk_ok(lean_box(0));
        return ts_errno_error("timestamp directory", errno);
    }
    int fd = -1;
    for (unsigned int attempt = 0; attempt < 2; attempt++) {
        fd = ts_owner_open(dir, name, (uid_t)owner_uid, create != 0);
        if (fd < 0)
            break;
        struct stat st;
        if (TEMP_FAILURE_RETRY(fstat(fd, &st)) != 0) {
            fd = ts_close_error(fd, errno);
            break;
        }
        if (attempt == 0 && ts_predates_boot(&st)) {
            (void)close(fd);
            fd = -1;
            if (TEMP_FAILURE_RETRY(unlinkat(dir, name, 0)) != 0 && errno != ENOENT)
                break;
            continue;
        }
        break;
    }
    int error = errno;
    (void)close(dir);
    if (fd < 0) {
        if (!create && error == ENOENT)
            return lean_io_result_mk_ok(lean_box(0));
        return ts_errno_error("timestamp open", error);
    }
    lean_object *some = lean_alloc_ctor(1, 1, 0);
    lean_ctor_set(some, 0, lean_box_uint32((uint32_t)fd));
    return lean_io_result_mk_ok(some);
}

static bool ts_valid_fd(uint32_t fd) {
    return fd <= INT_MAX;
}

static bool ts_valid_offset(uint64_t offset) {
    return offset <= INT64_MAX && (off_t)offset >= 0 &&
        (uint64_t)(off_t)offset == offset;
}

static lean_obj_res ts_read_extent(uint32_t fd, uint64_t offset, size_t length) {
    if (lean_alloc_sarray_would_overflow(1, length))
        return ts_errno_error("timestamp read", EOVERFLOW);
    lean_object *arr = lean_alloc_sarray(1, 0, length);
    size_t total = 0;
    while (total < length) {
        size_t count = length - total;
        if (count > SSIZE_MAX)
            count = SSIZE_MAX;
        ssize_t n = pread((int)fd, lean_sarray_cptr(arr) + total, count,
            (off_t)(offset + total));
        if (n < 0) {
            if (errno == EINTR)
                continue;
            int error = errno;
            lean_dec(arr);
            return ts_errno_error("timestamp read", error);
        }
        if (n == 0)
            break;
        total += (size_t)n;
    }
    lean_sarray_set_size(arr, total);
    return lean_io_result_mk_ok(arr);
}

LEAN_EXPORT lean_obj_res lean_sudo_ts_size(uint32_t fd, lean_obj_arg w) {
    (void)w;
    if (!ts_valid_fd(fd))
        return ts_errno_error("timestamp size", EBADF);
    struct stat st;
    if (TEMP_FAILURE_RETRY(fstat((int)fd, &st)) != 0)
        return ts_errno_error("timestamp size", errno);
    if (st.st_size < 0 || !ts_valid_offset((uint64_t)st.st_size))
        return ts_errno_error("timestamp size", EOVERFLOW);
    return lean_io_result_mk_ok(lean_box_uint64((uint64_t)st.st_size));
}

LEAN_EXPORT lean_obj_res lean_sudo_ts_read_at(uint32_t fd, uint64_t offset,
        uint32_t length, lean_obj_arg w) {
    (void)w;
    if (!ts_valid_fd(fd))
        return ts_errno_error("timestamp read", EBADF);
    if (!ts_valid_offset(offset) || length > (uint64_t)INT64_MAX - offset ||
            !ts_valid_offset(offset + length))
        return ts_errno_error("timestamp read", EOVERFLOW);
    return ts_read_extent(fd, offset, (size_t)length);
}

LEAN_EXPORT lean_obj_res lean_sudo_ts_pwrite(uint32_t fd, uint64_t offset,
        b_lean_obj_arg bytes, lean_obj_arg w) {
    (void)w;
    if (!ts_valid_fd(fd))
        return ts_errno_error("timestamp pwrite", EBADF);
    size_t length = lean_sarray_size(bytes);
    if (!ts_valid_offset(offset) || length > (uint64_t)INT64_MAX - offset ||
            !ts_valid_offset(offset + length))
        return ts_errno_error("timestamp pwrite", EOVERFLOW);
    const uint8_t *data = lean_sarray_cptr(bytes);
    size_t total = 0;
    while (total < length) {
        size_t count = length - total;
        if (count > SSIZE_MAX)
            count = SSIZE_MAX;
        ssize_t n = pwrite((int)fd, data + total, count, (off_t)(offset + total));
        if (n < 0) {
            if (errno == EINTR)
                continue;
            return ts_errno_error("timestamp pwrite", errno);
        }
        if (n == 0)
            return ts_errno_error("timestamp pwrite", EIO);
        total += (size_t)n;
    }
    return lean_io_result_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res lean_sudo_ts_truncate(uint32_t fd, uint64_t length,
        lean_obj_arg w) {
    (void)w;
    if (!ts_valid_fd(fd))
        return ts_errno_error("timestamp truncate", EBADF);
    if (!ts_valid_offset(length))
        return ts_errno_error("timestamp truncate", EOVERFLOW);
    int rc;
    rc = TEMP_FAILURE_RETRY(ftruncate((int)fd, (off_t)length));
    if (rc != 0)
        return ts_errno_error("timestamp truncate", errno);
    return lean_io_result_mk_ok(lean_box(0));
}

static pthread_mutex_t ts_signal_mutex = PTHREAD_MUTEX_INITIALIZER;
static _Atomic(pthread_t) ts_lock_thread;
static atomic_int ts_lock_signal;
static _Thread_local volatile sig_atomic_t ts_is_lock_thread;

static void ts_lock_handler(int signo) {
    int saved_errno = errno;
    if (ts_is_lock_thread) {
        atomic_store_explicit(&ts_lock_signal, signo, memory_order_relaxed);
    } else {
        (void)pthread_kill(atomic_load_explicit(&ts_lock_thread,
            memory_order_relaxed), signo);
    }
    errno = saved_errno;
}

static int ts_wait_lock(int fd, struct flock *region) {
    if (!atomic_is_lock_free(&ts_lock_thread) ||
            !atomic_is_lock_free(&ts_lock_signal)) {
        errno = ENOTSUP;
        return -1;
    }
    int error = pthread_mutex_lock(&ts_signal_mutex);
    if (error != 0) {
        errno = error;
        return -1;
    }
    sigset_t interrupts, saved_mask, wait_mask;
    sigemptyset(&interrupts);
    sigaddset(&interrupts, SIGINT);
    sigaddset(&interrupts, SIGQUIT);
    error = pthread_sigmask(SIG_BLOCK, &interrupts, &saved_mask);
    if (error != 0) {
        (void)pthread_mutex_unlock(&ts_signal_mutex);
        errno = error;
        return -1;
    }
    atomic_store_explicit(&ts_lock_thread, pthread_self(), memory_order_relaxed);
    atomic_store_explicit(&ts_lock_signal, 0, memory_order_relaxed);
    ts_is_lock_thread = 1;
    struct sigaction action, saved_int, saved_quit;
    memset(&action, 0, sizeof(action));
    action.sa_handler = ts_lock_handler;
    action.sa_mask = interrupts;
    bool installed_int = false, installed_quit = false, acquired = false;
    if (sigaction(SIGINT, &action, &saved_int) != 0) {
        error = errno;
        goto restore;
    }
    installed_int = true;
    if (sigaction(SIGQUIT, &action, &saved_quit) != 0) {
        error = errno;
        goto restore;
    }
    installed_quit = true;
    wait_mask = saved_mask;
    sigdelset(&wait_mask, SIGINT);
    sigdelset(&wait_mask, SIGQUIT);
    error = pthread_sigmask(SIG_SETMASK, &wait_mask, NULL);
    if (error != 0)
        goto restore;
    for (;;) {
        if (atomic_load_explicit(&ts_lock_signal, memory_order_relaxed) != 0) {
            error = EINTR;
            break;
        }
        if (fcntl(fd, F_SETLKW, region) == 0) {
            acquired = true;
            error = 0;
            break;
        }
        error = errno;
        if (error != EINTR ||
                atomic_load_explicit(&ts_lock_signal, memory_order_relaxed) != 0)
            break;
    }

restore:
    {
        int rc = pthread_sigmask(SIG_BLOCK, &interrupts, NULL);
        if (rc != 0 && error == 0)
            error = rc;
        if (installed_quit && sigaction(SIGQUIT, &saved_quit, NULL) != 0 &&
                error == 0)
            error = errno;
        if (installed_int && sigaction(SIGINT, &saved_int, NULL) != 0 &&
                error == 0)
            error = errno;
        int caught = atomic_load_explicit(&ts_lock_signal, memory_order_relaxed);
        if (caught != 0)
            error = EINTR;
        if (acquired && error != 0) {
            struct flock unlock = *region;
            unlock.l_type = F_UNLCK;
            rc = TEMP_FAILURE_RETRY(fcntl(fd, F_SETLK, &unlock));
        }
        ts_is_lock_thread = 0;
        if (caught != 0) {
            struct timespec immediate = {0, 0};
            while (sigtimedwait(&interrupts, NULL, &immediate) >= 0 ||
                    errno == EINTR) {
            }
            const struct sigaction *previous =
                caught == SIGINT ? &saved_int : &saved_quit;
            if (previous->sa_handler != SIG_DFL && previous->sa_handler != SIG_IGN) {
                sigset_t replay_mask = saved_mask;
                sigdelset(&replay_mask, caught);
                rc = pthread_kill(pthread_self(), caught);
                if (rc == 0)
                    rc = pthread_sigmask(SIG_SETMASK, &replay_mask, NULL);
                if (rc != 0)
                    error = rc;
            }
        }
        rc = pthread_sigmask(SIG_SETMASK, &saved_mask, NULL);
        if (rc != 0 && error == 0)
            error = rc;
    }
    (void)pthread_mutex_unlock(&ts_signal_mutex);
    errno = error;
    return error == 0 ? 0 : -1;
}

LEAN_EXPORT lean_obj_res lean_sudo_ts_lock(uint32_t fd, uint64_t offset,
        uint64_t length, uint8_t lock, lean_obj_arg w) {
    (void)w;
    if (!ts_valid_fd(fd))
        return ts_errno_error("timestamp lock", EBADF);
    if (!ts_valid_offset(offset) || !ts_valid_offset(length) ||
            length > (uint64_t)INT64_MAX - offset ||
            !ts_valid_offset(offset + length))
        return ts_errno_error("timestamp lock", EOVERFLOW);
    struct flock region;
    memset(&region, 0, sizeof(region));
    region.l_type = lock ? F_WRLCK : F_UNLCK;
    region.l_whence = SEEK_SET;
    region.l_start = (off_t)offset;
    region.l_len = (off_t)length;
    int rc;
    if (lock) {
        rc = ts_wait_lock((int)fd, &region);
    } else {
        rc = TEMP_FAILURE_RETRY(fcntl((int)fd, F_SETLK, &region));
    }
    if (rc != 0) {
        int error = errno;
        if (error == EINTR)
            return lean_io_result_mk_error(lean_mk_io_error_interrupted(
                lean_mk_string("timestamp lock"), (uint32_t)error,
                lean_mk_string(strerror(error))));
        return ts_errno_error("timestamp lock", error);
    }
    return lean_io_result_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res lean_sudo_ts_close(uint32_t fd, lean_obj_arg w) {
    (void)w;
    if (!ts_valid_fd(fd))
        return ts_errno_error("timestamp close", EBADF);
    if (close((int)fd) != 0 && errno != EINTR)
        return ts_errno_error("timestamp close", errno);
    return lean_io_result_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res lean_sudo_ts_remove(b_lean_obj_arg directory,
        b_lean_obj_arg filename, uint32_t owner_uid, uint32_t owner_gid,
        lean_obj_arg w) {
    (void)w;
    if (!ts_valid_args(directory, filename, owner_uid, owner_gid))
        return ts_errno_error("timestamp path or owner", EINVAL);
    int dir = ts_directory(lean_string_cstr(directory), (uid_t)owner_uid,
        (gid_t)owner_gid, false);
    if (dir < 0) {
        if (errno == ENOENT)
            return lean_io_result_mk_ok(lean_box(0));
        return ts_errno_error("timestamp directory", errno);
    }
    int rc = TEMP_FAILURE_RETRY(unlinkat(dir, lean_string_cstr(filename), 0));
    int error = errno;
    (void)close(dir);
    if (rc != 0 && error != ENOENT)
        return ts_errno_error("timestamp remove", error);
    return lean_io_result_mk_ok(lean_box(0));
}
