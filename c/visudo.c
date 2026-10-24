/*
 * lean-sudo C shim for visudo (LeanSudo.Visudo.Sys): locking the sudoers file,
 * creation/truncation of the temporary copy, and fixing its owner/mode before it is
 * renamed over the original.
 *
 * Conventions as in core.c: IO functions return a Lean IO result (no world
 * argument), string arguments are borrowed and rejected if they contain NUL.
 */
#include <lean/lean.h>

#include <errno.h>
#include <fcntl.h>
#include <signal.h>
#include <stdarg.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <sys/syscall.h>
#include <unistd.h>

static lean_obj_res io_err(const char *msg) {
    return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(msg)));
}

static lean_obj_res io_errno_path(const char *what, const char *path, int e) {
    char ebuf[256], buf[1024];
    snprintf(buf, sizeof buf, "%s%s%s: %s", what, *what ? " " : "", path,
        strerror_r(e, ebuf, sizeof ebuf));
    return io_err(buf);
}

static const char *cstr_arg(b_lean_obj_arg s) {
    const char *c = lean_string_cstr(s);
    if (strlen(c) != lean_string_size(s) - 1) return NULL;
    return c;
}

LEAN_EXPORT lean_obj_res leansudo_visudo_run_editor(b_lean_obj_arg path,
        b_lean_obj_arg args) {
    const char *p = cstr_arg(path);
    if (!p) return io_err("invalid editor");
    size_t argc = lean_array_size(args);
    char **argv = calloc(argc + 1, sizeof *argv);
    if (!argv) return io_err("unable to allocate memory");
    for (size_t i = 0; i < argc; i++) {
        argv[i] = (char *)cstr_arg(lean_array_get_core(args, i));
        if (!argv[i]) {
            free(argv);
            return io_err("invalid editor argument");
        }
    }
    pid_t pid = fork();
    if (pid == -1) {
        int e = errno;
        free(argv);
        return io_errno_path("unable to execute", p, e);
    }
    if (pid == 0) {
        if (syscall(SYS_close_range, (unsigned int)(STDERR_FILENO + 1), ~0U, 0) != 0) {
            long maxfd = sysconf(_SC_OPEN_MAX);
            if (maxfd < 0) _exit(127);
            for (long fd = STDERR_FILENO + 1; fd < maxfd; fd++) close((int)fd);
        }
        execv(p, argv);
        int ignored = dprintf(STDERR_FILENO, "visudo: unable to run %s: %s\n", p, strerror(errno));
        (void)ignored;
        _exit(127);
    }
    free(argv);
    int status;
    pid_t rv;
    do { rv = waitpid(pid, &status, 0); } while (rv == -1 && errno == EINTR);
    return lean_io_result_mk_ok(lean_box(rv != -1 && WIFEXITED(status)));
}

/* Keep every original descriptor open: OFD locks survive independent reads and
 * conflict with sudo.ws's POSIX record locks. */
struct locked_file {
    struct locked_file *next;
    char *path;
    int fd;
    dev_t dev;
    ino_t ino;
};
static struct locked_file *locked_files;

/* A missing original is created before locking, just as upstream does. */
LEAN_EXPORT lean_obj_res leansudo_visudo_lock(b_lean_obj_arg path, uint32_t mode) {
    const char *p = cstr_arg(path);
    if (!p) return io_err("invalid path");
    for (struct locked_file *l = locked_files; l; l = l->next)
        if (!strcmp(l->path, p)) return lean_io_result_mk_ok(lean_box(0));
    int fd = open(p, O_RDWR | O_NONBLOCK | O_NOCTTY | O_CLOEXEC);
    bool created = false;
    if (fd < 0 && errno == ENOENT) {
        fd = open(p, O_RDWR | O_CREAT | O_NONBLOCK | O_NOCTTY | O_CLOEXEC, mode);
        created = true;
    }
    if (fd < 0) return io_errno_path("", p, errno);
    struct stat st;
    if (fstat(fd, &st) != 0 || !S_ISREG(st.st_mode)) {
        close(fd);
        char buf[1024];
        snprintf(buf, sizeof buf, "%s is not a regular file", p);
        return io_err(buf);
    }
    for (struct locked_file *l = locked_files; l; l = l->next) {
        if (l->dev == st.st_dev && l->ino == st.st_ino) {
            close(fd);
            return lean_io_result_mk_ok(lean_box(0));
        }
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
    struct locked_file *l = malloc(sizeof *l);
    if (!l || !(l->path = strdup(p))) {
        free(l);
        close(fd);
        return io_err("unable to allocate memory");
    }
    l->fd = fd;
    l->dev = st.st_dev;
    l->ino = st.st_ino;
    l->next = locked_files;
    locked_files = l;
    return lean_io_result_mk_ok(lean_box(created ? 2 : 0));
}

struct temporary_file {
    struct temporary_file *next;
    char *path;
};
static struct temporary_file *temporary_files;

static void cleanup_signal(int signo) {
    for (struct temporary_file *t = temporary_files; t; t = t->next)
        unlink(t->path);
    const char prefix[] = "visudo exiting due to signal: ";
    const char *name = strsignal(signo);
    ssize_t ignored = write(STDERR_FILENO, prefix, sizeof prefix - 1);
    ignored = write(STDERR_FILENO, name, strlen(name));
    ignored = write(STDERR_FILENO, "\n", 1);
    (void)ignored;
    _exit(signo);
}

static bool track_temp(const char *path) {
    for (struct temporary_file *t = temporary_files; t; t = t->next)
        if (!strcmp(t->path, path)) return true;
    struct temporary_file *t = malloc(sizeof *t);
    if (!t || !(t->path = strdup(path))) {
        free(t);
        return false;
    }
    if (!temporary_files) {
        struct sigaction sa;
        memset(&sa, 0, sizeof sa);
        sigemptyset(&sa.sa_mask);
        sa.sa_flags = SA_RESTART;
        sa.sa_handler = cleanup_signal;
        sigaction(SIGTERM, &sa, NULL);
        sigaction(SIGHUP, &sa, NULL);
        sigaction(SIGINT, &sa, NULL);
        sigaction(SIGQUIT, &sa, NULL);
    }
    t->next = temporary_files;
    temporary_files = t;
    return true;
}

/* Reuse stale temporary files; the original's record lock excludes live edits. */
LEAN_EXPORT lean_obj_res leansudo_visudo_create_temp(b_lean_obj_arg path, b_lean_obj_arg content) {
    const char *p = cstr_arg(path);
    if (!p) return io_err("invalid path");
    if (!track_temp(p)) return io_err("unable to allocate memory");
    int fd = open(p, O_WRONLY | O_CREAT | O_TRUNC | O_NOCTTY | O_CLOEXEC, 0600);
    if (fd < 0) return io_errno_path("", p, errno);
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
    return lean_io_result_mk_ok(lean_box(0));
}

/* Preserve original mtime so an untouched editor buffer is distinguishable from
 * a rewrite with identical bytes. */
LEAN_EXPORT lean_obj_res leansudo_visudo_temp_time(b_lean_obj_arg original, b_lean_obj_arg temp) {
    const char *p = cstr_arg(original), *t = cstr_arg(temp);
    if (!p || !t) return io_err("invalid path");
    struct stat st;
    if (stat(p, &st) != 0) return io_errno_path("unable to stat", p, errno);
    struct timespec times[2] = { st.st_mtim, st.st_mtim };
    if (utimensat(AT_FDCWD, t, times, 0) != 0)
        return io_errno_path("unable to set time on", t, errno);
    return lean_io_result_mk_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res leansudo_visudo_modified(b_lean_obj_arg original, b_lean_obj_arg temp) {
    const char *p = cstr_arg(original), *t = cstr_arg(temp);
    if (!p || !t) return io_err("invalid path");
    struct stat a, b;
    if (stat(p, &a) != 0) return io_errno_path("unable to stat", p, errno);
    if (stat(t, &b) != 0) return io_errno_path("unable to stat", t, errno);
    bool changed = a.st_size != b.st_size || a.st_mtim.tv_sec != b.st_mtim.tv_sec ||
        a.st_mtim.tv_nsec != b.st_mtim.tv_nsec;
    return lean_io_result_mk_ok(lean_box(changed));
}

/* Upstream's compatibility option deliberately invokes cvtsudoers via PATH. */
LEAN_EXPORT lean_obj_res leansudo_visudo_export(b_lean_obj_arg input, b_lean_obj_arg output) {
    const char *in = cstr_arg(input), *out = cstr_arg(output);
    if (!in || !out) return io_err("invalid path");
    execlp("cvtsudoers", "cvtsudoers", "-f", "json", "-o", out, in, (char *)NULL);
    return io_errno_path("unable to execute", "cvtsudoers", errno);
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
