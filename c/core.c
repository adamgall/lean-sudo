/*
 * lean-sudo C shim: users/groups/host/tty/stat/realpath/secure read/environ/syslog
 * (LeanSudo.Sys.Core) and PAM (LeanSudo.Sys.Pam).
 *
 * Conventions:
 *  - Every IO function returns a Lean IO result (no world argument).
 *  - String arguments are borrowed (`@&`); strings containing NUL bytes are rejected
 *    instead of being silently truncated.
 *  - Strings handed to Lean are validated as UTF-8 first.
 *  - No Lean object is retained by C beyond a call.  The PAM handle is an external
 *    object whose data is a plain C struct (it owns C copies of the config strings).
 */
#include "shim.h"
#include "locale_scope.h"
#include "plugins.h"

#include <dirent.h>
#include <dlfcn.h>
#include <errno.h>
#include <fcntl.h>
#include <grp.h>
#include <limits.h>
#include <libintl.h>
#include <locale.h>
#include <poll.h>
#include <pthread.h>
#include <pwd.h>
#include <signal.h>
#include <stdarg.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <syslog.h>
#include <sys/wait.h>
#include <sys/file.h>
#include <sys/prctl.h>
#include <sys/ioctl.h>
#include <sys/utsname.h>
#include <sys/random.h>
#include <termios.h>
#include <time.h>
#include <unistd.h>

extern char **environ;

/* Keep the submitted TZ only for Lean's command-environment construction.
 * libc/PAM and all policy/logging clocks must use the system timezone.
 * Ubuntu's CVE-2026-96512.patch requires unsetenv, not a temporary environ
 * swap: mktime/localtime may consult TZ again after tzset. */
static char *submitted_tz;
static bool locale_initialized;

int lean_sudo_initialize_locale(void) {
    if (!locale_initialized) {
        const char *tz = getenv("TZ");
        if (tz && !(submitted_tz = strdup(tz))) return -1;
        locale_initialized = true;
    }
    if (unsetenv("TZ") != 0) return -1;
    tzset();
    (void)setlocale(LC_ALL, "");
    return 0;
}

/* ------------------------------------------------------------------------- */
/* Helpers                                                                    */
/* ------------------------------------------------------------------------- */

static lean_obj_res io_errno_path(const char *what, const char *path, int e) {
    char buf[256];
    return ls_errorf("%s %s: %s", what, path, strerror_r(e, buf, sizeof buf));
}


int ls_plugin_utf8_valid(const char *text, size_t size) {
    return ls_utf8_valid(text, size);
}


/* Lossy variant for informational text (PAM messages etc.). */
static lean_object *mk_str_lossy(const char *s) { return lean_mk_string_from_bytes(s, strlen(s)); }


static lean_obj_res mk_some(lean_obj_arg v) {
    lean_object *o = lean_alloc_ctor(1, 1, 0);
    lean_ctor_set(o, 0, v);
    return o;
}

static lean_obj_res mk_none(void) { return lean_box(0); }


static lean_obj_res mk_nat(uint64_t v) { return lean_uint64_to_nat(v); }


static int write_str(int fd, const char *s) { return ls_write_all(fd, s, strlen(s)); }

#define NUL_ARG_ERROR "argument contains a NUL byte"

/* ------------------------------------------------------------------------- */
/* Ids                                                                        */
/* ------------------------------------------------------------------------- */

LEAN_EXPORT lean_obj_res lean_sudo_getuid(void) { return ls_ok(mk_nat(getuid())); }
LEAN_EXPORT lean_obj_res lean_sudo_geteuid(void) { return ls_ok(mk_nat(geteuid())); }
LEAN_EXPORT lean_obj_res lean_sudo_getgid(void) { return ls_ok(mk_nat(getgid())); }
LEAN_EXPORT lean_obj_res lean_sudo_getegid(void) { return ls_ok(mk_nat(getegid())); }

LEAN_EXPORT lean_obj_res lean_sudo_set_uid(uint32_t uid) {
    if ((uintmax_t)(uid_t)uid != uid) return ls_errno(EINVAL);
    if (setuid((uid_t)uid) != 0) return ls_errno(errno);
    if (getuid() != (uid_t)uid || geteuid() != (uid_t)uid)
        return ls_errno(EPERM);
    return ls_ok(lean_box(0));
}

static lean_obj_res gid_array(const gid_t *g, size_t n) {
    lean_object *arr = lean_mk_empty_array_with_capacity(lean_box(n));
    for (size_t i = 0; i < n; i++) arr = lean_array_push(arr, mk_nat(g[i]));
    return arr;
}

LEAN_EXPORT lean_obj_res lean_sudo_valid_shells(void) {
    lean_object *shells = lean_mk_empty_array_with_capacity(lean_box(8));
    setusershell();
    const char *path;
    while ((path = getusershell()) != NULL) {
        lean_object *shell = ls_string(path);
        if (shell) shells = lean_array_push(shells, shell);
    }
    endusershell();
    return ls_ok(shells);
}

/* getgroups : IO (Array Nat) */
LEAN_EXPORT lean_obj_res lean_sudo_getgroups(void) {
    for (int attempt = 0; attempt < 8; attempt++) {
        int n = getgroups(0, NULL);
        if (n < 0) return ls_errno(errno);
        gid_t *g = malloc(sizeof(gid_t) * ((size_t)n + 1));
        if (!g) return ls_errno(ENOMEM);
        int m = getgroups(n + 1, g);
        if (m < 0) {
            int e = errno;
            free(g);
            if (e == EINVAL) continue; /* group list grew between calls */
            return ls_errno(e);
        }
        lean_object *arr = gid_array(g, (size_t)m);
        free(g);
        return ls_ok(arr);
    }
    return ls_errno(EINVAL);
}

/* ------------------------------------------------------------------------- */
/* passwd / group                                                             */
/* ------------------------------------------------------------------------- */

#define NSS_BUF_MAX ((size_t)64 << 20)

static size_t nss_initial(int which) {
    long v = sysconf(which);
    if (v <= 0 || v > 1 << 20) return 4096;
    return (size_t)v;
}

/* "not found" errors as documented in getpwnam_r(3) */
static bool nss_not_found(int rc) {
    return rc == 0 || rc == ENOENT || rc == ESRCH || rc == EBADF || rc == EPERM;
}

/* Passwd: ctor 0, fields name uid gid gecos home shell (all boxed). */
static lean_obj_res pw_lookup(const char *name, uid_t uid) {
    size_t sz = nss_initial(_SC_GETPW_R_SIZE_MAX);
    for (;;) {
        char *buf = malloc(sz);
        if (!buf) return ls_errno(ENOMEM);
        struct passwd pw, *res = NULL;
        int rc = name ? getpwnam_r(name, &pw, buf, sz, &res) : getpwuid_r(uid, &pw, buf, sz, &res);
        if (rc == ERANGE && sz < NSS_BUF_MAX) { free(buf); sz *= 2; continue; }
        if (rc == EINTR) { free(buf); continue; }
        if (res == NULL) {
            free(buf);
            if (nss_not_found(rc)) return ls_ok(mk_none());
            return ls_errno(rc);
        }
        lean_object *pname = ls_string(pw.pw_name);
        lean_object *home = ls_string(pw.pw_dir ? pw.pw_dir : "");
        lean_object *shell = ls_string(pw.pw_shell ? pw.pw_shell : "");
        lean_object *gecos = mk_str_lossy(pw.pw_gecos ? pw.pw_gecos : "");
        uid_t pu = pw.pw_uid;
        gid_t pg = pw.pw_gid;
        free(buf);
        if (!pname || !home || !shell) {
            if (pname) lean_dec(pname);
            if (home) lean_dec(home);
            if (shell) lean_dec(shell);
            lean_dec(gecos);
            return ls_error("passwd entry is not valid UTF-8");
        }
        lean_object *o = lean_alloc_ctor(0, 6, 0);
        lean_ctor_set(o, 0, pname);
        lean_ctor_set(o, 1, mk_nat(pu));
        lean_ctor_set(o, 2, mk_nat(pg));
        lean_ctor_set(o, 3, gecos);
        lean_ctor_set(o, 4, home);
        lean_ctor_set(o, 5, shell);
        return ls_ok(mk_some(o));
    }
}

LEAN_EXPORT lean_obj_res lean_sudo_getpwnam(b_lean_obj_arg name) {
    const char *n = ls_cstr(name);
    if (!n) return ls_ok(mk_none());
    return pw_lookup(n, 0);
}

LEAN_EXPORT lean_obj_res lean_sudo_getpwuid(uint32_t uid) { return pw_lookup(NULL, (uid_t)uid); }

/* Returns Option (String × Nat) */
static lean_obj_res gr_lookup(const char *name, gid_t gid) {
    size_t sz = nss_initial(_SC_GETGR_R_SIZE_MAX);
    for (;;) {
        char *buf = malloc(sz);
        if (!buf) return ls_errno(ENOMEM);
        struct group gr, *res = NULL;
        int rc = name ? getgrnam_r(name, &gr, buf, sz, &res) : getgrgid_r(gid, &gr, buf, sz, &res);
        if (rc == ERANGE && sz < NSS_BUF_MAX) { free(buf); sz *= 2; continue; }
        if (rc == EINTR) { free(buf); continue; }
        if (res == NULL) {
            free(buf);
            if (nss_not_found(rc)) return ls_ok(mk_none());
            return ls_errno(rc);
        }
        lean_object *gname = ls_string(gr.gr_name);
        gid_t g = gr.gr_gid;
        free(buf);
        if (!gname) return ls_error("group entry is not valid UTF-8");
        return ls_ok(mk_some(ls_pair(gname, mk_nat(g))));
    }
}

LEAN_EXPORT lean_obj_res lean_sudo_getgrnam(b_lean_obj_arg name) {
    const char *n = ls_cstr(name);
    if (!n) return ls_ok(mk_none());
    return gr_lookup(n, 0);
}

LEAN_EXPORT lean_obj_res lean_sudo_getgrgid(uint32_t gid) { return gr_lookup(NULL, (gid_t)gid); }

/* getgrouplist : String → UInt32 → IO (Array Nat) */
LEAN_EXPORT lean_obj_res lean_sudo_getgrouplist(b_lean_obj_arg user, uint32_t gid) {
    const char *u = ls_cstr(user);
    if (!u) return ls_error(NUL_ARG_ERROR);
    int n = 64;
    for (;;) {
        gid_t *g = malloc(sizeof(gid_t) * (size_t)n);
        if (!g) return ls_errno(ENOMEM);
        int cnt = n;
        int rc = getgrouplist(u, (gid_t)gid, g, &cnt);
        if (rc >= 0) {
            if (cnt > n) cnt = n;
            lean_object *arr = gid_array(g, (size_t)cnt);
            free(g);
            return ls_ok(arr);
        }
        free(g);
        int next = cnt > n ? cnt : n * 2;
        if (next > (1 << 20)) return ls_error("getgrouplist: too many groups");
        n = next;
    }
}

/* ------------------------------------------------------------------------- */
/* host / tty / environ                                                       */
/* ------------------------------------------------------------------------- */

LEAN_EXPORT lean_obj_res lean_sudo_gethostname(void) {
    char buf[HOST_NAME_MAX + 2];
    memset(buf, 0, sizeof buf);
    if (gethostname(buf, HOST_NAME_MAX + 1) != 0) return ls_errno(errno);
    buf[HOST_NAME_MAX + 1] = '\0';
    lean_object *s = ls_string(buf);
    if (!s) return ls_error("host name is not valid UTF-8");
    return ls_ok(s);
}

LEAN_EXPORT lean_obj_res lean_sudo_isatty(uint32_t fd) {
    return ls_ok(lean_box(isatty((int)fd) ? 1 : 0));
}

LEAN_EXPORT lean_obj_res lean_sudo_ttyname(uint32_t fd) {
    char buf[PATH_MAX];
    if (ttyname_r((int)fd, buf, sizeof buf) != 0) return ls_ok(mk_none());
    buf[sizeof buf - 1] = '\0';
    lean_object *s = ls_string(buf);
    return ls_ok(s ? mk_some(s) : mk_none());
}

static lean_object *push_env_pair(lean_object *arr, const char *entry, bool process_env) {
    const char *eq = strchr(entry, '=');
    if (!eq) return arr;
    size_t klen = (size_t)(eq - entry), vlen = strlen(eq + 1);
    if (process_env ? locale_initialized && klen == 2 && memcmp(entry, "TZ", 2) == 0
                    : klen == 0) return arr;
    if (!ls_utf8_valid(entry, klen) || !ls_utf8_valid(eq + 1, vlen)) return arr;
    return lean_array_push(arr, ls_pair(lean_mk_string_from_bytes_unchecked(entry, klen),
        lean_mk_string_from_bytes_unchecked(eq + 1, vlen)));
}

/* environ : IO (Array (String × String)); drops entries without '=' or not UTF-8 */
LEAN_EXPORT lean_obj_res lean_sudo_environ(void) {
    lean_object *arr = lean_mk_empty_array();
    for (char **e = environ; e && *e; e++)
        arr = push_env_pair(arr, *e, true);
    if (submitted_tz) {
        lean_object *val = ls_string(submitted_tz);
        if (val) arr = lean_array_push(arr, ls_pair(lean_mk_string("TZ"), val));
    }
    return ls_ok(arr);
}

/* ------------------------------------------------------------------------- */
/* Files                                                                      */
/* ------------------------------------------------------------------------- */

/* FileStat: ctor 0, fields dev ino mode uid gid size rdev (all boxed Nat). */
static lean_obj_res mk_filestat(const struct stat *st) {
    lean_object *o = lean_alloc_ctor(0, 7, 0);
    lean_ctor_set(o, 0, mk_nat((uint64_t)st->st_dev));
    lean_ctor_set(o, 1, mk_nat((uint64_t)st->st_ino));
    lean_ctor_set(o, 2, mk_nat((uint64_t)st->st_mode));
    lean_ctor_set(o, 3, mk_nat((uint64_t)st->st_uid));
    lean_ctor_set(o, 4, mk_nat((uint64_t)st->st_gid));
    lean_ctor_set(o, 5, mk_nat(st->st_size < 0 ? 0 : (uint64_t)st->st_size));
    lean_ctor_set(o, 6, mk_nat((uint64_t)st->st_rdev));
    return o;
}

LEAN_EXPORT lean_obj_res lean_sudo_stat(b_lean_obj_arg path) {
    const char *p = ls_cstr(path);
    struct stat st;
    if (!p || stat(p, &st) != 0) return ls_ok(mk_none());
    return ls_ok(mk_some(mk_filestat(&st)));
}

LEAN_EXPORT lean_obj_res lean_sudo_lstat(b_lean_obj_arg path) {
    const char *p = ls_cstr(path);
    struct stat st;
    if (!p || lstat(p, &st) != 0) return ls_ok(mk_none());
    return ls_ok(mk_some(mk_filestat(&st)));
}

LEAN_EXPORT lean_obj_res lean_sudo_realpath(b_lean_obj_arg path) {
    const char *p = ls_cstr(path);
    if (!p) return ls_ok(mk_none());
    char *r = realpath(p, NULL);
    if (!r) return ls_ok(mk_none());
    lean_object *s = ls_string(r);
    free(r);
    return ls_ok(s ? mk_some(s) : mk_none());
}

LEAN_EXPORT lean_obj_res lean_sudo_access(b_lean_obj_arg path, uint32_t mode) {
    const char *p = ls_cstr(path);
    if (!p) return ls_ok(lean_box(0));
    return ls_ok(lean_box(access(p, (int)mode) == 0 ? 1 : 0));
}

#define READ_CAP ((size_t)16 << 20)

/* readFileNoFollow : String → IO (FileStat × String) */
static lean_obj_res read_file(b_lean_obj_arg path, bool follow) {
    const char *p = ls_cstr(path);
    if (!p) return ls_error(NUL_ARG_ERROR);
    int fd;
    do {
        fd = open(p, O_RDONLY | (follow ? 0 : O_NOFOLLOW) | O_CLOEXEC | O_NONBLOCK | O_NOCTTY);
    } while (fd < 0 && errno == EINTR);
    if (fd < 0) return io_errno_path("unable to open", p, errno);
    struct stat st;
    if (fstat(fd, &st) != 0) {
        int e = errno;
        close(fd);
        return io_errno_path("unable to stat", p, e);
    }
    if (!S_ISREG(st.st_mode)) {
        close(fd);
        return ls_errorf("%s is not a regular file", p);
    }
    if (st.st_size < 0 || (size_t)st.st_size > READ_CAP) {
        close(fd);
        return ls_errorf("%s: file too large", p);
    }
    size_t cap = (size_t)st.st_size + 1; /* +1 to detect growth */
    char *buf = malloc(cap);
    if (!buf) { close(fd); return ls_errno(ENOMEM); }
    size_t len = 0;
    for (;;) {
        if (len == cap) {
            if (cap > READ_CAP) {
                free(buf);
                close(fd);
                return ls_errorf("%s: file too large", p);
            }
            size_t ncap = cap * 2 > READ_CAP + 1 ? READ_CAP + 1 : cap * 2;
            char *nb = realloc(buf, ncap);
            if (!nb) { free(buf); close(fd); return ls_errno(ENOMEM); }
            buf = nb;
            cap = ncap;
        }
        ssize_t k = read(fd, buf + len, cap - len);
        if (k < 0) {
            if (errno == EINTR) continue;
            int e = errno;
            free(buf);
            close(fd);
            return io_errno_path("unable to read", p, e);
        }
        if (k == 0) break;
        len += (size_t)k;
    }
    close(fd);
    if (len > READ_CAP) {
        free(buf);
        return ls_errorf("%s: file too large", p);
    }
    lean_object *s = ls_string_n(buf, len);
    free(buf);
    if (!s) return ls_errorf("%s: file is not valid UTF-8", p);
    return ls_ok(ls_pair(mk_filestat(&st), s));
}

LEAN_EXPORT lean_obj_res lean_sudo_read_file_nofollow(b_lean_obj_arg path) {
    return read_file(path, false);
}

LEAN_EXPORT lean_obj_res lean_sudo_read_file_follow(b_lean_obj_arg path) {
    return read_file(path, true);
}

/* listDir : String → IO (Array String) — names excluding . and .., unsorted */
LEAN_EXPORT lean_obj_res lean_sudo_list_dir(b_lean_obj_arg path) {
    const char *p = ls_cstr(path);
    if (!p) return ls_error(NUL_ARG_ERROR);
    int fd = open(p, O_RDONLY | O_DIRECTORY | O_CLOEXEC);
    if (fd < 0) return io_errno_path("unable to open", p, errno);
    DIR *d = fdopendir(fd);
    if (!d) {
        int e = errno;
        close(fd);
        return io_errno_path("unable to open", p, e);
    }
    lean_object *arr = lean_mk_empty_array();
    for (;;) {
        errno = 0;
        struct dirent *de = readdir(d);
        if (!de) {
            int e = errno;
            closedir(d);
            if (e != 0) {
                lean_dec(arr);
                return io_errno_path("unable to read", p, e);
            }
            return ls_ok(arr);
        }
        if (strcmp(de->d_name, ".") == 0 || strcmp(de->d_name, "..") == 0) continue;
        lean_object *s = ls_string(de->d_name);
        if (!s) {
            closedir(d);
            lean_dec(arr);
            return ls_errorf("%s: directory entry name is not valid UTF-8", p);
        }
        arr = lean_array_push(arr, s);
    }
}

LEAN_EXPORT lean_obj_res lean_sudo_getcwd(void) {
    char *c = getcwd(NULL, 0);
    if (!c) return ls_errno(errno);
    lean_object *s = ls_string(c);
    free(c);
    if (!s) return ls_error("current directory is not valid UTF-8");
    return ls_ok(s);
}

/* umask : UInt32 → IO UInt32 — sets the mask, returns the previous one */
LEAN_EXPORT lean_obj_res lean_sudo_umask(uint32_t mask) {
    return ls_ok(lean_box_uint32((uint32_t)umask((mode_t)(mask & 07777))));
}

LEAN_EXPORT lean_obj_res lean_sudo_write_stderr(b_lean_obj_arg s) {
    if (ls_write_all(STDERR_FILENO, lean_string_cstr(s), lean_string_size(s) - 1) != 0)
        return ls_errno(errno);
    return ls_ok(lean_box(0));
}

/* ------------------------------------------------------------------------- */
/* syslog                                                                     */
/* ------------------------------------------------------------------------- */

struct name_val { const char *name; int val; };

static const struct name_val facilities[] = {
    {"authpriv", LOG_AUTHPRIV}, {"auth", LOG_AUTH}, {"daemon", LOG_DAEMON},
    {"user", LOG_USER}, {"local0", LOG_LOCAL0}, {"local1", LOG_LOCAL1},
    {"local2", LOG_LOCAL2}, {"local3", LOG_LOCAL3}, {"local4", LOG_LOCAL4},
    {"local5", LOG_LOCAL5}, {"local6", LOG_LOCAL6}, {"local7", LOG_LOCAL7},
    {NULL, 0}};

static const struct name_val priorities[] = {
    {"alert", LOG_ALERT}, {"crit", LOG_CRIT}, {"err", LOG_ERR},
    {"warning", LOG_WARNING}, {"notice", LOG_NOTICE}, {"info", LOG_INFO},
    {"debug", LOG_DEBUG}, {NULL, 0}};

static bool lookup_name(const struct name_val *t, const char *n, int *out) {
    for (; t->name; t++)
        if (strcmp(t->name, n) == 0) { *out = t->val; return true; }
    return false;
}

LEAN_EXPORT lean_obj_res lean_sudo_syslog(b_lean_obj_arg facility, b_lean_obj_arg priority,
                                          b_lean_obj_arg msg) {
    int fac, pri;
    const char *f = ls_cstr(facility), *p = ls_cstr(priority);
    if (!f || !lookup_name(facilities, f, &fac)) return ls_error("unknown syslog facility");
    if (!p || !lookup_name(priorities, p, &pri)) return ls_error("unknown syslog priority");
    /* A NUL in the message just truncates it, which is harmless for logging. */
    openlog("sudo", LOG_PID, fac);
    syslog(fac | pri, "%s", lean_string_cstr(msg));
    closelog();
    return ls_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res lean_sudo_syslog_bytes(b_lean_obj_arg facility,
        b_lean_obj_arg priority, b_lean_obj_arg bytes, uint8_t pid) {
    int fac, pri;
    const char *f = ls_cstr(facility), *p = ls_cstr(priority);
    if (!f || !lookup_name(facilities, f, &fac)) return ls_error("unknown syslog facility");
    if (!p || !lookup_name(priorities, p, &pri)) return ls_error("unknown syslog priority");
    size_t n = lean_sarray_size(bytes);
    if (n > INT_MAX || memchr(lean_sarray_cptr(bytes), 0, n))
        return ls_error("invalid syslog message");
    openlog("sudo", pid ? LOG_PID : 0, fac);
    syslog(fac | pri, "%.*s", (int)n, (const char *)lean_sarray_cptr(bytes));
    closelog();
    return ls_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res lean_sudo_unix_time(void) {
    time_t now = time(NULL);
    if (now < 0) return ls_errno(errno);
    return ls_ok(mk_nat((uint64_t)now));
}

LEAN_EXPORT lean_obj_res lean_sudo_terminal_columns(uint32_t fd) {
    if (fd > INT_MAX) return ls_error("invalid terminal descriptor");
    struct stat st;
    if (fstat((int)fd, &st) == 0 && S_ISFIFO(st.st_mode)) return ls_ok(mk_nat(0));
    struct winsize ws;
    unsigned int columns = 80;
    if (ioctl((int)fd, TIOCGWINSZ, &ws) == 0 && ws.ws_col) columns = ws.ws_col;
    return ls_ok(mk_nat(columns));
}

/* Recover civil fields encoded without a zone, then let the system timezone
 * resolve this date's DST rules, including gaps/folds, just like gentime.c.
 * The caller's TZ has already been removed by locale initialization. */
LEAN_EXPORT lean_obj_res lean_sudo_local_civil_epoch(b_lean_obj_arg civil) {
    if (!lean_is_scalar(civil)) return ls_ok(mk_none());
    uint64_t value = lean_unbox(civil);
    time_t encoded = (time_t)value;
    if (encoded < 0 || (uint64_t)encoded != value) return ls_ok(mk_none());
    struct tm tm;
    if (!gmtime_r(&encoded, &tm)) return ls_ok(mk_none());
    tm.tm_isdst = -1;
    time_t epoch = mktime(&tm);
    if (epoch == (time_t)-1) return ls_ok(mk_none());
    return ls_ok(mk_some(lean_int64_to_int((int64_t)epoch)));
}

LEAN_EXPORT lean_obj_res lean_sudo_architecture(void) {
    struct utsname u;
    if (uname(&u) != 0) return ls_errno(errno);
    return ls_ok(mk_str_lossy(u.machine));
}


LEAN_EXPORT lean_obj_res lean_sudo_no_new_privs(void) {
    return ls_ok(lean_box(prctl(PR_GET_NO_NEW_PRIVS, 0, 0, 0, 0) == 1));
}

static lean_obj_res open_readonly(b_lean_obj_arg path, bool regular) {
    const char *p = ls_cstr(path);
    if (!p) return ls_error(NUL_ARG_ERROR);
    int fd = open(p, O_RDONLY | O_CLOEXEC | O_NONBLOCK | O_NOCTTY);
    if (fd < 0) return io_errno_path("unable to open", p, errno);
    struct stat st;
    if (fstat(fd, &st) != 0) {
        int saved = errno;
        close(fd);
        return io_errno_path("unable to stat", p, saved);
    }
    if (regular && !S_ISREG(st.st_mode)) {
        close(fd);
        return ls_error("command is not a regular file");
    }
    if (fd < 3) {
        int copy = fcntl(fd, F_DUPFD_CLOEXEC, 3);
        close(fd);
        if (copy < 0) return ls_errno(errno);
        fd = copy;
    }
    return ls_ok(ls_pair(mk_nat((uint64_t)fd), mk_filestat(&st)));
}

LEAN_EXPORT lean_obj_res lean_sudo_open_command(b_lean_obj_arg path) {
    return open_readonly(path, true);
}

LEAN_EXPORT lean_obj_res lean_sudo_open_readonly(b_lean_obj_arg path) {
    return open_readonly(path, false);
}

LEAN_EXPORT lean_obj_res lean_sudo_close_descriptor(uint32_t fd) {
    if (fd < 3 || fd > INT_MAX) return ls_error("invalid file descriptor");
    if (close((int)fd) != 0) return ls_errno(errno);
    return ls_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res lean_sudo_admin_flag(b_lean_obj_arg path,
        uint32_t uid, uint32_t gid, b_lean_obj_arg groups) {
    const char *p = ls_cstr(path);
    if (!p || uid == UINT32_MAX || gid == UINT32_MAX)
        return ls_error("invalid admin flag arguments");
    size_t n = lean_array_size(groups);
    gid_t *gs = calloc(n ? n : 1, 2 * sizeof(*gs));
    if (!gs) return ls_errno(ENOMEM);
    for (size_t i = 0; i < n; i++) {
        b_lean_obj_arg g = lean_array_get_core(groups, i);
        if (!lean_is_scalar(g) || lean_unbox(g) >= UINT32_MAX) {
            free(gs); return ls_error("invalid admin flag group");
        }
        gs[i] = (gid_t)lean_unbox(g);
    }
    qsort(gs, n, sizeof(*gs), ls_compare_gid);
    pid_t pid = fork();
    if (pid == 0) {
        if (ls_drop_credentials(uid, gid, gs, n, gs + n)) _exit(1);
        int fd = open(p, O_WRONLY | O_CREAT | O_EXCL | O_NOFOLLOW | O_CLOEXEC, 0644);
        if (fd < 0) _exit(errno == EEXIST ? 0 : 1);
        _exit(close(fd) == 0 ? 0 : 1);
    }
    free(gs);
    if (pid < 0) return ls_errno(errno);
    int status;
    while (waitpid(pid, &status, 0) < 0) if (errno != EINTR) return ls_errno(errno);
    if (!WIFEXITED(status) || WEXITSTATUS(status) != 0)
        return ls_error("unable to create admin flag");
    return ls_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res lean_sudo_log_time(uint8_t year, b_lean_obj_arg locale_name) {
    const char *name = ls_cstr(locale_name);
    if (!name) return ls_error(NUL_ARG_ERROR);
    locale_t previous;
    locale_t locale = leansudo_locale_enter(name, &previous);
    if (!locale) return ls_error("unable to initialize logging locale");
    time_t now = time(NULL);
    struct tm tm;
    char buf[64];
    bool ok = localtime_r(&now, &tm) &&
        strftime(buf, sizeof(buf), year ? "%b %e %H:%M:%S %Y" : "%b %e %H:%M:%S", &tm);
    leansudo_locale_leave(locale, previous);
    if (!ok) return ls_error("unable to format log timestamp");
    return ls_ok(lean_mk_string(buf));
}

LEAN_EXPORT lean_obj_res lean_sudo_event_time(uint8_t year, b_lean_obj_arg locale_name) {
    struct timespec ts;
    struct tm tm;
    char iso[64] = "", local[64] = "";
    if (clock_gettime(CLOCK_REALTIME, &ts) != 0) return ls_errno(errno);
    const char *name = ls_cstr(locale_name);
    if (!name) return ls_error(NUL_ARG_ERROR);
    locale_t previous;
    locale_t locale = leansudo_locale_enter(name, &previous);
    if (!locale) return ls_error("unable to initialize logging locale");
    bool ok = gmtime_r(&ts.tv_sec, &tm) &&
        strftime(iso, sizeof(iso), "%Y%m%d%H%M%SZ", &tm) &&
        localtime_r(&ts.tv_sec, &tm) &&
        strftime(local, sizeof(local), year ? "%b %e %H:%M:%S %Y" : "%b %e %H:%M:%S", &tm);
    leansudo_locale_leave(locale, previous);
    if (!ok) return ls_error("unable to format event timestamp");
    lean_object *v = lean_alloc_ctor(0, 4, 0);
    lean_ctor_set(v, 0, mk_nat((uint64_t)ts.tv_sec));
    lean_ctor_set(v, 1, mk_nat((uint64_t)ts.tv_nsec));
    lean_ctor_set(v, 2, lean_mk_string(iso));
    lean_ctor_set(v, 3, lean_mk_string(local));
    return ls_ok(v);
}

LEAN_EXPORT lean_obj_res lean_sudo_event_uuid(void) {
    unsigned char bytes[16];
    size_t done = 0;
    while (done < sizeof(bytes)) {
        ssize_t n = getrandom(bytes + done, sizeof(bytes) - done, 0);
        if (n < 0) { if (errno == EINTR) continue; return ls_errno(errno); }
        if (n == 0) return ls_error("unable to generate event UUID");
        done += (size_t)n;
    }
    bytes[7] = (bytes[7] & 0x0f) | 0x40;
    bytes[8] = (bytes[8] & 0x3f) | 0x80;
    /* sudo_uuid_to_string uses a 10-4-4-4-10 layout. */
    char uuid[37], *p = uuid;
    const char hex[] = "0123456789abcdef";
    for (size_t i = 0; i < sizeof(bytes); i++) {
        if (i == 5 || i == 7 || i == 9 || i == 11) *p++ = '-';
        *p++ = hex[bytes[i] >> 4]; *p++ = hex[bytes[i] & 15];
    }
    *p = '\0';
    return ls_ok(lean_mk_string(uuid));
}

LEAN_EXPORT lean_obj_res lean_sudo_terminal_size(void) {
    struct winsize ws = {0};
    int fd = open("/dev/tty", O_RDONLY | O_NOCTTY | O_CLOEXEC | O_NONBLOCK);
    if (fd >= 0) { (void)ioctl(fd, TIOCGWINSZ, &ws); close(fd); }
    return ls_ok(ls_pair(mk_nat(ws.ws_col ? ws.ws_col : 80),
        mk_nat(ws.ws_row ? ws.ws_row : 24)));
}

LEAN_EXPORT lean_obj_res lean_sudo_signal_name(uint32_t sig) {
    const char *name = NULL;
    switch (sig) {
#define SIGNAL_NAME(s) case SIG##s: name = #s; break
    SIGNAL_NAME(HUP); SIGNAL_NAME(INT); SIGNAL_NAME(QUIT); SIGNAL_NAME(ILL);
    SIGNAL_NAME(TRAP); SIGNAL_NAME(ABRT); SIGNAL_NAME(BUS); SIGNAL_NAME(FPE);
    SIGNAL_NAME(KILL); SIGNAL_NAME(USR1); SIGNAL_NAME(SEGV); SIGNAL_NAME(USR2);
    SIGNAL_NAME(PIPE); SIGNAL_NAME(ALRM); SIGNAL_NAME(TERM); SIGNAL_NAME(STKFLT);
    SIGNAL_NAME(CHLD); SIGNAL_NAME(CONT); SIGNAL_NAME(STOP); SIGNAL_NAME(TSTP);
    SIGNAL_NAME(TTIN); SIGNAL_NAME(TTOU); SIGNAL_NAME(URG); SIGNAL_NAME(XCPU);
    SIGNAL_NAME(XFSZ); SIGNAL_NAME(VTALRM); SIGNAL_NAME(PROF); SIGNAL_NAME(WINCH);
    SIGNAL_NAME(IO); SIGNAL_NAME(PWR); SIGNAL_NAME(SYS);
#undef SIGNAL_NAME
    }
    if (name) return ls_ok(lean_mk_string(name));
    char buf[32];
    if (sig == (uint32_t)SIGRTMIN) snprintf(buf, sizeof(buf), "RTMIN");
    else if (sig == (uint32_t)SIGRTMAX) snprintf(buf, sizeof(buf), "RTMAX");
    else if (sig > (uint32_t)SIGRTMIN && sig < (uint32_t)SIGRTMAX)
        snprintf(buf, sizeof(buf), "RTMIN+%u", sig - (uint32_t)SIGRTMIN);
    else snprintf(buf, sizeof(buf), "%u", sig);
    return ls_ok(lean_mk_string(buf));
}

static lean_obj_res append_log(b_lean_obj_arg path, b_lean_obj_arg text, bool json) {
    const char *p = ls_cstr(path), *s = ls_cstr(text);
    if (!p || !s) return ls_error(NUL_ARG_ERROR);
    int flags = json ? O_RDWR : O_WRONLY | O_APPEND;
    int fd = open(p, flags | O_CREAT | O_NOFOLLOW | O_CLOEXEC | O_NONBLOCK, 0600);
    if (fd < 0) return io_errno_path("unable to open log file", p, errno);
    struct stat st;
    if ((json && flock(fd, LOCK_EX) != 0) || fstat(fd, &st) != 0 ||
        !S_ISREG(st.st_mode) || st.st_uid != 0 || (st.st_mode & 022) ||
        (!json && flock(fd, LOCK_EX) != 0)) {
        close(fd); return ls_error("unsafe or inaccessible log file");
    }
    int rc = 0;
    if (json) {
        if (st.st_size == 0) {
            rc = ls_write_all(fd, "{", 1);
        } else {
            rc = lseek(fd, -3, SEEK_END) < 0 ? -1 : ls_write_all(fd, ",", 1);
        }
    }
    if (rc == 0) rc = ls_write_all(fd, s, strlen(s));
    if (rc == 0 && json) rc = ls_write_all(fd, "\n}\n", 3);
    int saved = errno;
    close(fd);
    if (rc != 0) return ls_errno(saved);
    return ls_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res lean_sudo_append_json(b_lean_obj_arg path, b_lean_obj_arg member) {
    return append_log(path, member, true);
}

LEAN_EXPORT lean_obj_res lean_sudo_append_log(b_lean_obj_arg path, b_lean_obj_arg text) {
    return append_log(path, text, false);
}

LEAN_EXPORT lean_obj_res lean_sudo_send_mail(b_lean_obj_arg path, b_lean_obj_arg args,
        b_lean_obj_arg body) {
    const char *p = ls_cstr(path), *text = ls_cstr(body);
    if (!p || !text) return ls_error(NUL_ARG_ERROR);
    size_t count = lean_array_size(args);
    if (count > 63) return ls_error("too many mailer flags");
    char **argv = calloc(count + 2, sizeof(*argv));
    if (!argv) return ls_errno(ENOMEM);
    const char *base = strrchr(p, '/');
    argv[0] = (char *)(base ? base + 1 : p);
    for (size_t i = 0; i < count; i++) {
        argv[i + 1] = (char *)ls_cstr(lean_array_get_core(args, i));
        if (!argv[i + 1]) { free(argv); return ls_error(NUL_ARG_ERROR); }
    }
    int fds[2];
    if (pipe2(fds, O_CLOEXEC) != 0) { free(argv); return ls_errno(errno); }
    uid_t uid = getuid();
    gid_t gid = getgid();
    int ngroups = getgroups(0, NULL);
    gid_t *groups = ngroups < 0 ? NULL : calloc((size_t)ngroups + 1, 2 * sizeof(*groups));
    if (!groups || getgroups(ngroups, groups) != ngroups) {
        free(groups); free(argv); close(fds[0]); close(fds[1]);
        return ls_error("unable to get mailer groups");
    }
    qsort(groups, (size_t)ngroups, sizeof(*groups), ls_compare_gid);
    pid_t pid = fork();
    if (pid == 0) {
        close(fds[1]);
        if (dup2(fds[0], STDIN_FILENO) < 0) _exit(126);
        int nullfd = open("/dev/null", O_RDWR);
        if (nullfd < 0 || dup2(nullfd, 1) < 0 || dup2(nullfd, 2) < 0) _exit(126);
        if (ls_drop_credentials(uid, gid, groups, (size_t)ngroups, groups + ngroups)) _exit(126);
        if (chdir("/") != 0) _exit(126);
        if (ls_close_from(3)) _exit(126);
        execve(p, argv, environ);
        _exit(127);
    }
    close(fds[0]);
    free(argv);
    free(groups);
    if (pid < 0) { close(fds[1]); return ls_errno(errno); }
    struct sigaction ignore = {.sa_handler = SIG_IGN}, old;
    sigemptyset(&ignore.sa_mask);
    if (sigaction(SIGPIPE, &ignore, &old) != 0) {
        close(fds[1]); kill(pid, SIGKILL);
        while (waitpid(pid, NULL, 0) < 0 && errno == EINTR) {}
        return ls_error("unable to protect mail pipe");
    }
    int rc = ls_write_all(fds[1], text, strlen(text));
    close(fds[1]);
    (void)sigaction(SIGPIPE, &old, NULL);
    int status;
    while (waitpid(pid, &status, 0) < 0) if (errno != EINTR) return ls_errno(errno);
    if (rc != 0 || !WIFEXITED(status) || WEXITSTATUS(status) != 0)
        return ls_error("unable to send mail");
    return ls_ok(lean_box(0));
}

/* ========================================================================= */
/* PAM                                                                        */
/* ========================================================================= */

/* Linux-PAM ABI (security/_pam_types.h) */
typedef struct pam_handle pam_handle_t;
struct pam_message { int msg_style; const char *msg; };
struct pam_response { char *resp; int resp_retcode; };
struct pam_conv {
    int (*conv)(int, const struct pam_message **, struct pam_response **, void *);
    void *appdata_ptr;
};

#define PAM_SUCCESS 0
#define PAM_BUF_ERR 5
#define PAM_PERM_DENIED 6
#define PAM_AUTH_ERR 7
#define PAM_USER_UNKNOWN 10
#define PAM_MAXTRIES 11
#define PAM_NEW_AUTHTOK_REQD 12
#define PAM_CONV_ERR 19

#define PAM_PROMPT_ECHO_OFF 1
#define PAM_PROMPT_ECHO_ON 2
#define PAM_ERROR_MSG 3
#define PAM_TEXT_INFO 4

#define PAM_SILENT 0x8000
#define PAM_ESTABLISH_CRED 0x0002
#define PAM_DELETE_CRED 0x0004
#define PAM_REINITIALIZE_CRED 0x0008
#define PAM_CHANGE_EXPIRED_AUTHTOK 0x0020

#define PAM_TTY 3
#define PAM_RHOST 4
#define PAM_USER 2
#define PAM_RUSER 8

#define PAM_MAX_NUM_MSG 32
#define PAM_PW_MAX 1024

static struct {
    int (*start)(const char *, const char *, const struct pam_conv *, pam_handle_t **);
    int (*end)(pam_handle_t *, int);
    int (*authenticate)(pam_handle_t *, int);
    int (*acct_mgmt)(pam_handle_t *, int);
    int (*chauthtok)(pam_handle_t *, int);
    int (*setcred)(pam_handle_t *, int);
    int (*open_session)(pam_handle_t *, int);
    int (*close_session)(pam_handle_t *, int);
    char **(*getenvlist)(pam_handle_t *);
    const char *(*strerror)(pam_handle_t *, int);
    int (*set_item)(pam_handle_t *, int, const void *);
    int (*get_item)(const pam_handle_t *, int, const void **);
} pamfn;

static bool pam_loaded;
static char pam_load_error[512];
static pthread_once_t pam_load_once = PTHREAD_ONCE_INIT;

static void pam_load(void) {
    void *h = dlopen("libpam.so.0", RTLD_NOW | RTLD_LOCAL);
    if (!h) {
        const char *e = dlerror();
        snprintf(pam_load_error, sizeof pam_load_error, "unable to load libpam.so.0: %s",
                 e ? e : "unknown error");
        return;
    }
    const struct ls_symbol syms[] = {
        {"pam_start", (void *)&pamfn.start},
        {"pam_end", (void *)&pamfn.end},
        {"pam_authenticate", (void *)&pamfn.authenticate},
        {"pam_acct_mgmt", (void *)&pamfn.acct_mgmt},
        {"pam_chauthtok", (void *)&pamfn.chauthtok},
        {"pam_setcred", (void *)&pamfn.setcred},
        {"pam_open_session", (void *)&pamfn.open_session},
        {"pam_close_session", (void *)&pamfn.close_session},
        {"pam_getenvlist", (void *)&pamfn.getenvlist},
        {"pam_strerror", (void *)&pamfn.strerror},
        {"pam_set_item", (void *)&pamfn.set_item},
        {"pam_get_item", (void *)&pamfn.get_item},
    };
    const char *missing = ls_dlsyms(h, syms, sizeof syms / sizeof syms[0]);
    if (missing) {
        snprintf(pam_load_error, sizeof pam_load_error,
            "libpam.so.0: missing symbol %s", missing);
        memset(&pamfn, 0, sizeof pamfn);
        dlclose(h);
        return;
    }
    pam_loaded = true;
}

static bool pam_ensure_loaded(void) {
    pthread_once(&pam_load_once, pam_load);
    return pam_loaded;
}

LEAN_EXPORT lean_obj_res lean_sudo_pam_available(void) {
    return ls_ok(lean_box(pam_ensure_loaded() ? 1 : 0));
}

/* Conversation error codes (see conv_error_message). */
enum {
    CONV_OK = 0,
    CONV_ERR_NONINTERACTIVE,
    CONV_ERR_NO_TTY,
    CONV_ERR_TIMEOUT,
    CONV_ERR_NO_PASSWORD,
    CONV_ERR_READ,
    CONV_ERR_NOMEM,
    CONV_ERR_BAD_MESSAGE,
};

static const char *conv_error_message(int code) {
    switch (code) {
    case CONV_ERR_NONINTERACTIVE: return "a password is required";
    case CONV_ERR_NO_TTY:
        if (getenv("SSH_CONNECTION") && !getenv("SSH_TTY"))
            return "a terminal is required to read the password; either use ssh's -t option or configure an askpass helper";
        return "a terminal is required to read the password; either use the -S option to "
               "read from standard input or configure an askpass helper";
    case CONV_ERR_TIMEOUT: return "timed out reading password";
    case CONV_ERR_NO_PASSWORD: return "no password was provided";
    case CONV_ERR_READ: return "unable to read password";
    case CONV_ERR_NOMEM: return "unable to allocate memory";
    case CONV_ERR_BAD_MESSAGE: return "unsupported PAM conversation message";
    default: return NULL;
    }
}

typedef struct {
    pam_handle_t *pamh;
    bool ended;
    int last_status;
    struct pam_conv conv;
    bool use_stdin, noninteractive, override, pwfeedback, visiblepw;
    uint32_t timeout;
    char *prompt;
    char *user, *ruser, *askpass, *lecture;
    bool silent, session_silent, bell, lectured;
    uid_t askpass_uid;
    gid_t askpass_gid;
    gid_t *askpass_groups;
    int askpass_ngroups;
    int conv_error;
    int interrupted;
} sudo_pam_t;

/* --- terminal handling during password reads --- */

static volatile sig_atomic_t tty_active;
static volatile sig_atomic_t tty_interrupted;
static int tty_fd = -1;
static struct sudo_conv_callback *plugin_conv_callback;
static volatile sig_atomic_t plugin_conv_stop;
static volatile sig_atomic_t plugin_conv_active, plugin_conv_has_callback;
static struct termios tty_saved, tty_noecho;

static const int tty_sigs[] = {SIGINT, SIGQUIT, SIGTERM, SIGHUP, SIGTSTP, SIGTTIN, SIGTTOU};
#define N_TTY_SIGS (sizeof tty_sigs / sizeof tty_sigs[0])
static struct sigaction tty_old_actions[N_TTY_SIGS];
static bool tty_installed[N_TTY_SIGS];
/* A signal may land on another Lean runtime thread, so EINTR alone cannot
 * wake the thread waiting for a password. Keep one close-on-exec self-pipe
 * for the process lifetime, avoiding close/reuse races with the handler. */
static int tty_wakeup[2] = {-1, -1};

static int tty_prepare_wakeup(void) {
    if (tty_wakeup[0] < 0 && pipe2(tty_wakeup, O_NONBLOCK | O_CLOEXEC) != 0)
        return -1;
    char bytes[64];
    for (;;) {
        ssize_t n = read(tty_wakeup[0], bytes, sizeof bytes);
        if (n > 0 || (n < 0 && errno == EINTR)) continue;
        return n < 0 && errno == EAGAIN ? 0 : -1;
    }
}

static void tty_sig_handler(int sig);

static void tty_install_one(size_t i) {
    struct sigaction sa;
    memset(&sa, 0, sizeof sa);
    sa.sa_handler = tty_sig_handler;
    sigemptyset(&sa.sa_mask);
    sa.sa_flags = 0; /* no SA_RESTART: interrupt poll/read so we re-check */
    sigaction(tty_sigs[i], &sa, NULL);
}

/* Interrupts return through PAM so Lean can report prior failed attempts.
 * Other signals retain their normal action; job-control stops re-arm echo
 * suppression after continuing. Async-signal-safe. */
static void tty_sig_handler(int sig) {
    int saved_errno = errno;
    if (tty_active) tcsetattr(tty_fd, TCSANOW, &tty_saved);
    if (plugin_conv_has_callback && (sig == SIGTSTP || sig == SIGTTIN || sig == SIGTTOU)) {
        plugin_conv_stop = sig;
        const char byte = 0;
        while (write(tty_wakeup[1], &byte, 1) < 0 && errno == EINTR) {}
        errno = saved_errno;
        return;
    }
    if (sig == SIGINT || sig == SIGQUIT) {
        tty_interrupted = sig;
        const char byte = 0;
        /* EAGAIN means a wakeup is already queued; the pipe is never closed. */
        while (write(tty_wakeup[1], &byte, 1) < 0 && errno == EINTR) {}
        errno = saved_errno;
        return;
    }
    struct sigaction dfl;
    memset(&dfl, 0, sizeof dfl);
    dfl.sa_handler = SIG_DFL;
    sigemptyset(&dfl.sa_mask);
    sigaction(sig, &dfl, NULL);
    sigset_t set;
    sigemptyset(&set);
    sigaddset(&set, sig);
    sigprocmask(SIG_UNBLOCK, &set, NULL);
    raise(sig);
    /* Only reached for stop signals after SIGCONT. */
    for (size_t i = 0; i < N_TTY_SIGS; i++)
        if (tty_sigs[i] == sig) tty_install_one(i);
    if (tty_active) tcsetattr(tty_fd, TCSANOW, &tty_noecho);
    errno = saved_errno;
}

static void tty_install_handlers(void) {
    for (size_t i = 0; i < N_TTY_SIGS; i++) {
        tty_installed[i] = false;
        if (sigaction(tty_sigs[i], NULL, &tty_old_actions[i]) != 0) continue;
        if (tty_old_actions[i].sa_handler == SIG_IGN) continue; /* keep ignored signals ignored */
        tty_install_one(i);
        tty_installed[i] = true;
    }
}

static void tty_restore_handlers(void) {
    for (size_t i = 0; i < N_TTY_SIGS; i++)
        if (tty_installed[i]) sigaction(tty_sigs[i], &tty_old_actions[i], NULL);
}


/* The helper is unprivileged and never receives privileged descriptors. */
static int read_askpass(sudo_pam_t *st, const char *prompt, char *buf, size_t size) {
    int fds[2];
    if (pipe2(fds, O_CLOEXEC) != 0) return CONV_ERR_READ;
    pid_t pid = fork();
    if (pid < 0) { close(fds[0]); close(fds[1]); return CONV_ERR_READ; }
    if (pid == 0) {
        close(fds[0]);
        if (dup2(fds[1], STDOUT_FILENO) < 0) _exit(126);
        int nullfd = open("/dev/null", O_RDONLY);
        if (nullfd < 0 || dup2(nullfd, STDIN_FILENO) < 0) _exit(126);
        uid_t uid = st->askpass_uid;
        gid_t gid = st->askpass_gid;
        gid_t *groups = st->askpass_groups;
        size_t n = (size_t)st->askpass_ngroups;
        if (ls_drop_credentials(uid, gid, groups, n, groups ? groups + n : NULL)) _exit(126);
        if (ls_close_from(3)) _exit(126);
        execl(st->askpass, st->askpass, prompt, (char *)NULL);
        _exit(127);
    }
    close(fds[1]);
    size_t n = 0;
    int result = CONV_OK;
    int64_t deadline = st->timeout ? ls_mono_ms() + (int64_t)st->timeout * 1000 : 0;
    for (;;) {
        int timeout = -1;
        if (deadline) {
            int64_t left = deadline - ls_mono_ms();
            if (left <= 0) { result = CONV_ERR_TIMEOUT; break; }
            timeout = left > INT_MAX ? INT_MAX : (int)left;
        }
        struct pollfd pfd = {.fd = fds[0], .events = POLLIN};
        int rc = poll(&pfd, 1, timeout);
        if (rc < 0 && errno == EINTR) continue;
        if (rc <= 0) { result = rc == 0 ? CONV_ERR_TIMEOUT : CONV_ERR_READ; break; }
        char c;
        ssize_t k = read(fds[0], &c, 1);
        if (k < 0 && errno == EINTR) continue;
        if (k < 0) { result = CONV_ERR_READ; break; }
        if (k == 0 || c == '\n') break;
        if (n < size - 1) buf[n++] = c;
    }
    close(fds[0]);
    if (result != CONV_OK) kill(pid, SIGKILL);
    int status;
    while (waitpid(pid, &status, 0) < 0) {
        if (errno != EINTR) { result = CONV_ERR_READ; break; }
    }
    buf[n] = '\0';
    if (result == CONV_OK && n == 0) result = CONV_ERR_NO_PASSWORD;
    if (result != CONV_OK) explicit_bzero(buf, size);
    return result;
}

static int plugin_prompt_suspend(void) {
    int signo = plugin_conv_stop, ret = 0;
    plugin_conv_stop = 0;
    struct sudo_conv_callback *cb = plugin_conv_callback;
    if (cb->on_suspend && cb->on_suspend(signo, cb->closure) == -1) ret = -1;
    /* Never execute plugin callbacks from a signal handler. */
    struct sigaction dfl = {0}, old;
    dfl.sa_handler = SIG_DFL;
    sigemptyset(&dfl.sa_mask);
    if (sigaction(signo, &dfl, &old) != 0) return -1;
    raise(signo);
    sigaction(signo, &old, NULL);
    if (cb->on_resume && cb->on_resume(signo, cb->closure) == -1) ret = -1;
    return ret;
}

/* Read one line into buf (NUL-terminated, newline stripped). Returns CONV_OK or an error. */
static int read_password(sudo_pam_t *st, const char *prompt, bool echo, char *buf, size_t size) {
    int in, out, own_fd = -1;
    if (st->askpass) return read_askpass(st, prompt, buf, size);
    if (st->use_stdin) {
        in = STDIN_FILENO;
        out = STDERR_FILENO;
    } else {
        own_fd = open("/dev/tty", O_RDWR | O_NOCTTY | O_CLOEXEC);
        if (own_fd < 0) {
            if (!echo && !st->visiblepw) return CONV_ERR_NO_TTY;
            in = STDIN_FILENO;
            out = STDERR_FILENO;
        } else {
            in = out = own_fd;
        }
    }

    bool noecho = false, feedback = false;
    struct termios saved;
    memset(&saved, 0, sizeof saved);
    if (tty_prepare_wakeup() != 0) {
        if (own_fd >= 0) close(own_fd);
        return CONV_ERR_READ;
    }
    sigset_t interrupts, oldmask;
    sigemptyset(&interrupts);
    sigaddset(&interrupts, SIGINT);
    sigaddset(&interrupts, SIGQUIT);
    tty_interrupted = 0;
    tty_fd = in;
    tty_install_handlers();
    if (sigprocmask(SIG_UNBLOCK, &interrupts, &oldmask) != 0) {
        tty_restore_handlers();
        if (own_fd >= 0) close(own_fd);
        return CONV_ERR_READ;
    }
    if (!echo && tcgetattr(in, &saved) == 0) {
        struct termios t = saved;
        t.c_lflag &= ~(tcflag_t)(ECHO | ECHONL);
        if (st->pwfeedback && own_fd >= 0) {
            t.c_lflag &= ~(tcflag_t)(ICANON | IEXTEN);
            t.c_cc[VMIN] = 1;
            t.c_cc[VTIME] = 0;
        }
        tty_fd = in;
        tty_saved = saved;
        tty_noecho = t;
        int rc;
        for (;;) {
            rc = tcsetattr(in, TCSADRAIN, &t);
            if (plugin_conv_stop) {
                if (plugin_prompt_suspend() != 0) goto read_failed;
                continue;
            }
            if (rc == 0 || errno != EINTR || tty_interrupted) break;
        }
        if (rc == 0) {
            tty_active = 1;
            noecho = true;
            feedback = st->pwfeedback && own_fd >= 0;
        }
    }
    if (plugin_conv_active && !echo && !noecho && !st->use_stdin && !st->visiblepw)
        goto read_failed;

    if (st->bell && own_fd >= 0) (void)write_str(out, "\a");
    (void)write_str(out, prompt);

    int64_t deadline = st->timeout > 0 ? ls_mono_ms() + (int64_t)st->timeout * 1000 : 0;
    size_t n = 0;
    bool got_any = false;
    int result = CONV_OK;
    for (;;) {
        if (plugin_conv_stop) {
            if (plugin_prompt_suspend() != 0) { result = CONV_ERR_READ; break; }
            if (noecho && tcsetattr(in, TCSANOW, &tty_noecho) != 0) {
                result = CONV_ERR_READ; break;
            }
            if (tty_prepare_wakeup() != 0) { result = CONV_ERR_READ; break; }
        }
        if (tty_interrupted) { result = CONV_ERR_NO_PASSWORD; break; }
        struct pollfd pfds[2] = {
            {.fd = in, .events = POLLIN},
            {.fd = tty_wakeup[0], .events = POLLIN}
        };
        int remaining = -1;
        if (deadline) {
            int64_t left = deadline - ls_mono_ms();
            if (left <= 0) { result = CONV_ERR_TIMEOUT; break; }
            remaining = left > INT_MAX ? INT_MAX : (int)left;
        }
        int pr = poll(pfds, 2, remaining);
        if (pr < 0) {
            if (errno == EINTR) continue;
            result = CONV_ERR_READ;
            break;
        }
        if (pr == 0) { result = CONV_ERR_TIMEOUT; break; }
        if (tty_interrupted) { result = CONV_ERR_NO_PASSWORD; break; }
        if (plugin_conv_stop) continue;
        char c;
        ssize_t k = read(in, &c, 1);
        if (k < 0) {
            if (errno == EINTR || errno == EAGAIN) continue;
            result = CONV_ERR_READ;
            break;
        }
        if (k == 0) {
            if (!got_any) result = CONV_ERR_NO_PASSWORD;
            break;
        }
        got_any = true;
        if (c == '\n' || (feedback && c == '\r')) break;
        if (feedback) {
            if ((cc_t)c == saved.c_cc[VERASE] || c == 0x7f || c == 0x08) {
                if (n > 0) {
                    /* drop one UTF-8 character */
                    while (n > 0 && ((unsigned char)buf[n - 1] & 0xC0) == 0x80) n--;
                    if (n > 0) n--;
                    (void)write_str(out, "\b \b");
                }
                continue;
            }
            if ((cc_t)c == saved.c_cc[VKILL]) {
                while (n > 0) {
                    while (n > 0 && ((unsigned char)buf[n - 1] & 0xC0) == 0x80) n--;
                    if (n > 0) n--;
                    (void)write_str(out, "\b \b");
                }
                continue;
            }
            if ((cc_t)c == saved.c_cc[VEOF]) {
                if (n == 0) result = CONV_ERR_NO_PASSWORD;
                break;
            }
        }
        if (n < size - 1) {
            buf[n++] = c;
            if (feedback && ((unsigned char)c & 0xC0) != 0x80) (void)write_str(out, "*");
        }
    }
    buf[n] = '\0';

    if (noecho) {
        while (tcsetattr(in, TCSADRAIN, &saved) != 0 && errno == EINTR) {}
        tty_active = 0;
        (void)write_str(out, "\n");
    }
    (void)sigprocmask(SIG_SETMASK, &oldmask, NULL);
    tty_restore_handlers();
    tty_fd = -1;
    explicit_bzero(&tty_saved, sizeof tty_saved);
    st->interrupted = tty_interrupted;
    if (st->interrupted) result = CONV_ERR_NO_PASSWORD;
    if (own_fd >= 0) close(own_fd);
    if (result != CONV_OK) explicit_bzero(buf, size);
    return result;

read_failed:
    (void)sigprocmask(SIG_SETMASK, &oldmask, NULL);
    tty_restore_handlers();
    tty_fd = -1;
    if (own_fd >= 0) close(own_fd);
    return CONV_ERR_READ;
}

static sudo_pam_t plugin_prompt;
static int pam_askpass_identity(sudo_pam_t *st);

int ls_plugin_conversation_config(int bell, const char *askpass) {
    char *copy = askpass && *askpass ? strdup(askpass) : NULL;
    if (askpass && *askpass && !copy) return -1;
    if (copy) {
        int err = pam_askpass_identity(&plugin_prompt);
        if (err) { free(copy); errno = err; return -1; }
    } else {
        free(plugin_prompt.askpass_groups);
        plugin_prompt.askpass_groups = NULL;
        plugin_prompt.askpass_ngroups = 0;
    }
    free(plugin_prompt.askpass);
    plugin_prompt.askpass = copy;
    plugin_prompt.bell = bell;
    return 0;
}

/* Share PAM's bounded, signal-safe terminal reader with plugin conversations. */
int ls_plugin_read_reply(const char *prompt, int type, unsigned timeout,
    int use_stdin, char *buf, size_t size, struct sudo_conv_callback *callback) {
    if (plugin_conv_active) {
        errno = EINVAL;
        return -1;
    }
    if (callback && SUDO_API_VERSION_GET_MAJOR(callback->version) != 1) callback = NULL;
    sudo_pam_t st = plugin_prompt;
    st.use_stdin = use_stdin;
    st.timeout = timeout;
    st.pwfeedback = (type & 0xff) == SUDO_CONV_PROMPT_MASK;
    st.visiblepw = (type & SUDO_CONV_PROMPT_ECHO_OK) != 0;
    plugin_conv_callback = callback;
    plugin_conv_stop = 0;
    plugin_conv_active = 1;
    plugin_conv_has_callback = callback != NULL;
    int ret = read_password(&st, prompt,
        (type & 0xff) == SUDO_CONV_PROMPT_ECHO_ON, buf, size);
    plugin_conv_has_callback = 0;
    plugin_conv_active = 0;
    plugin_conv_callback = NULL;
    plugin_conv_stop = 0;
    if (ret != CONV_OK) {
        const char *message = conv_error_message(ret);
        if (message) fprintf(stderr, "sudo: %s\n", message);
        errno = ret == CONV_ERR_TIMEOUT ? ETIMEDOUT : EIO;
        return -1;
    }
    return 0;
}

static bool is_generic_password_prompt(const char *p) {
    return p && (strcmp(p, "Password:") == 0 || strcmp(p, "Password: ") == 0);
}

/* sudo auth/pam.c distinguishes the literal sudo prompt from the translated
 * Linux-PAM generic prompt (challenge/response prompts must pass through). */
static bool is_generic_pam_password_prompt(const char *p) {
    return p && (is_generic_password_prompt(p) ||
        strcmp(p, dgettext("Linux-PAM", "Password:")) == 0 ||
        strcmp(p, dgettext("Linux-PAM", "Password: ")) == 0);
}

static bool use_sudo_prompt(const sudo_pam_t *st, const char *p) {
    if (st->override) return true;
    if (is_generic_password_prompt(st->prompt)) return false;
    if (is_generic_pam_password_prompt(p)) return true;
    size_t n = strlen(st->ruser);
    return p && strncmp(p, st->ruser, n) == 0 &&
        (strcmp(p + n, "'s Password:") == 0 || strcmp(p + n, "'s Password: ") == 0);
}

static int sudo_conv(int num_msg, const struct pam_message **msg, struct pam_response **resp,
                     void *appdata) {
    sudo_pam_t *st = appdata;
    if (!st || !resp || !msg || num_msg <= 0 || num_msg > PAM_MAX_NUM_MSG) return PAM_CONV_ERR;
    *resp = NULL;
    struct pam_response *r = calloc((size_t)num_msg, sizeof *r);
    if (!r) {
        st->conv_error = CONV_ERR_NOMEM;
        return PAM_BUF_ERR;
    }
    int rc = PAM_CONV_ERR;
    for (int i = 0; i < num_msg; i++) {
        const struct pam_message *m = msg[i];
        if (!m) goto fail;
        switch (m->msg_style) {
        case PAM_PROMPT_ECHO_OFF:
        case PAM_PROMPT_ECHO_ON: {
            if (st->noninteractive) {
                st->conv_error = CONV_ERR_NONINTERACTIVE;
                goto fail;
            }
            if (st->lecture && !st->lectured) {
                int fd = open("/dev/tty", O_WRONLY | O_NOCTTY | O_CLOEXEC);
                (void)write_str(fd >= 0 ? fd : STDERR_FILENO, st->lecture);
                if (fd >= 0) close(fd);
                st->lectured = true;
            }
            bool echo = m->msg_style == PAM_PROMPT_ECHO_ON;
            const char *prompt = m->msg ? m->msg : "";
            if (use_sudo_prompt(st, prompt)) prompt = st->prompt;
            char buf[PAM_PW_MAX];
            int err = read_password(st, prompt, echo, buf, sizeof buf);
            if (err != CONV_OK) {
                st->conv_error = err;
                goto fail;
            }
            r[i].resp = strdup(buf);
            explicit_bzero(buf, sizeof buf);
            if (!r[i].resp) {
                st->conv_error = CONV_ERR_NOMEM;
                rc = PAM_BUF_ERR;
                goto fail;
            }
            r[i].resp_retcode = 0;
            break;
        }
        case PAM_ERROR_MSG:
        case PAM_TEXT_INFO:
            if (m->msg) {
                int fd = open("/dev/tty", O_WRONLY | O_NOCTTY | O_CLOEXEC);
                int out = fd >= 0 ? fd : STDERR_FILENO;
                (void)write_str(out, m->msg);
                (void)write_str(out, "\n");
                if (fd >= 0) close(fd);
            }
            break;
        default:
            st->conv_error = CONV_ERR_BAD_MESSAGE;
            goto fail;
        }
    }
    *resp = r;
    return PAM_SUCCESS;
fail:
    for (int i = 0; i < num_msg; i++) {
        if (r[i].resp) {
            explicit_bzero(r[i].resp, strlen(r[i].resp));
            free(r[i].resp);
        }
    }
    free(r);
    return rc;
}

/* --- external object --- */

static void sudo_pam_free(sudo_pam_t *st) {
    if (st->prompt) {
        explicit_bzero(st->prompt, strlen(st->prompt));
        free(st->prompt);
    }
    free(st->user);
    free(st->ruser);
    free(st->askpass);
    free(st->lecture);
    free(st->askpass_groups);
    free(st);
}

static void pam_finalize(void *p) {
    sudo_pam_t *st = p;
    if (!st->ended && st->pamh) pamfn.end(st->pamh, st->last_status);
    sudo_pam_free(st);
}

static void pam_foreach(void *p, b_lean_obj_arg f) {
    (void)p;
    (void)f;
}

static lean_external_class *pam_class;
static pthread_once_t pam_class_once = PTHREAD_ONCE_INIT;

static void pam_class_init(void) { pam_class = lean_register_external_class(pam_finalize, pam_foreach); }

static sudo_pam_t *pam_data(b_lean_obj_arg h) { return (sudo_pam_t *)lean_get_external_data(h); }

static lean_obj_res pam_start_fail(sudo_pam_t *st, int rc) {
    const char *msg = pamfn.strerror(st->pamh, rc);
    lean_obj_res res = ls_errorf("unable to initialize PAM: %s", msg ? msg : "unknown error");
    if (st->pamh) pamfn.end(st->pamh, rc);
    sudo_pam_free(st);
    return res;
}

/* pamStartRaw (service user : @& String) (useStdin nonInteractive : Bool) (prompt : @& String)
 *   (override pwfeedback : Bool) (timeout : UInt32) (ruser : @& String) (tty : @& Option String) (visiblepw : Bool)
 *   : IO PamHandle */
LEAN_EXPORT lean_obj_res lean_sudo_pam_start(b_lean_obj_arg service, b_lean_obj_arg user,
                                             uint8_t use_stdin, uint8_t noninteractive,
                                             b_lean_obj_arg prompt, uint8_t override,
                                             uint8_t pwfeedback, uint32_t timeout,
                                             b_lean_obj_arg ruser, b_lean_obj_arg tty,
                                             uint8_t visiblepw) {
    if (!pam_ensure_loaded()) return ls_error(pam_load_error);
    const char *svc = ls_cstr(service), *usr = ls_cstr(user), *pr = ls_cstr(prompt),
               *ru = ls_cstr(ruser);
    const char *tt = NULL;
    if (!lean_is_scalar(tty)) {
        tt = ls_cstr(lean_ctor_get(tty, 0));
        if (!tt) return ls_error(NUL_ARG_ERROR);
    }
    if (!svc || !usr || !pr || !ru) return ls_error(NUL_ARG_ERROR);

    pthread_once(&pam_class_once, pam_class_init);
    sudo_pam_t *st = calloc(1, sizeof *st);
    if (!st) return ls_errno(ENOMEM);
    st->prompt = strdup(pr);
    if (!st->prompt) { free(st); return ls_errno(ENOMEM); }
    st->user = strdup(usr);
    st->ruser = strdup(ru);
    if (!st->user || !st->ruser) { sudo_pam_free(st); return ls_errno(ENOMEM); }
    st->silent = st->session_silent = true;
    st->use_stdin = use_stdin;
    st->noninteractive = noninteractive;
    st->override = override;
    st->pwfeedback = pwfeedback;
    st->visiblepw = visiblepw;
    st->timeout = timeout;
    st->conv.conv = sudo_conv;
    st->conv.appdata_ptr = st;

    int rc = pamfn.start(svc, usr, &st->conv, &st->pamh);
    if (rc != PAM_SUCCESS) return pam_start_fail(st, rc);
    if (*ru) (void)pamfn.set_item(st->pamh, PAM_RUSER, ru);
    if (tt) (void)pamfn.set_item(st->pamh, PAM_TTY, tt);
    return ls_ok(lean_alloc_external(pam_class, st));
}

LEAN_EXPORT lean_obj_res lean_sudo_pam_interrupted(b_lean_obj_arg h) {
    return ls_ok(lean_box_uint32((uint32_t)pam_data(h)->interrupted));
}

/* Capture before PAM or sudoedit changes process credentials. */
static int pam_askpass_identity(sudo_pam_t *st) {
    int n = getgroups(0, NULL);
    if (n < 0) return errno;
    gid_t *groups = n ? calloc((size_t)n, 2 * sizeof(*groups)) : NULL;
    if (n && !groups) return ENOMEM;
    if (n) {
        n = getgroups(n, groups);
        if (n < 0) { int error = errno; free(groups); return error; }
        qsort(groups, (size_t)n, sizeof(*groups), ls_compare_gid);
    }
    free(st->askpass_groups);
    st->askpass_groups = groups;
    st->askpass_ngroups = n;
    st->askpass_uid = getuid();
    st->askpass_gid = getgid();
    return 0;
}

LEAN_EXPORT lean_obj_res lean_sudo_pam_configure(b_lean_obj_arg h, uint8_t silent,
        uint8_t session_silent, uint8_t bell, b_lean_obj_arg askpass, b_lean_obj_arg rhost,
        b_lean_obj_arg prompt_user) {
    sudo_pam_t *st = pam_data(h);
    if (st->ended) return ls_error("PAM handle already ended");
    const char *ap = ls_cstr(askpass), *rh = ls_cstr(rhost), *pu = ls_cstr(prompt_user);
    if (!ap || !rh || !pu) return ls_error(NUL_ARG_ERROR);
    char *copy = *ap ? strdup(ap) : NULL;
    if (*ap && !copy) return ls_errno(ENOMEM);
    char *user_copy = strdup(pu);
    if (!user_copy) { free(copy); return ls_errno(ENOMEM); }
    if (copy) {
        int error = pam_askpass_identity(st);
        if (error) { free(copy); free(user_copy); return ls_errno(error); }
    }
    free(st->ruser);
    st->ruser = user_copy;
    free(st->askpass);
    st->askpass = copy;
    st->silent = silent;
    st->session_silent = session_silent;
    st->bell = bell;
    if (*rh) (void)pamfn.set_item(st->pamh, PAM_RHOST, rh);
    return ls_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res lean_sudo_pam_lecture(b_lean_obj_arg h, b_lean_obj_arg text) {
    sudo_pam_t *st = pam_data(h);
    if (st->ended) return ls_error("PAM handle already ended");
    const char *s = ls_cstr(text);
    if (!s) return ls_error(NUL_ARG_ERROR);
    char *copy = *s ? strdup(s) : NULL;
    if (*s && !copy) return ls_errno(ENOMEM);
    free(st->lecture);
    st->lecture = copy;
    return ls_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res lean_sudo_pam_lectured(b_lean_obj_arg h) {
    return ls_ok(lean_box(pam_data(h)->lectured));
}

static lean_obj_res pam_call(b_lean_obj_arg h, int (*fn)(pam_handle_t *, int),
                             int flags, bool check_user) {
    sudo_pam_t *st = pam_data(h);
    if (st->ended) return ls_error("PAM handle already ended");
    st->conv_error = CONV_OK;
    st->interrupted = 0;
    int rc = fn(st->pamh, flags);
    if (rc == PAM_SUCCESS && check_user) {
        const void *user = NULL;
        if (pamfn.get_item(st->pamh, PAM_USER, &user) != PAM_SUCCESS ||
            !user || strcmp(user, st->user) != 0) rc = PAM_AUTH_ERR;
    }
    st->last_status = rc;
    return ls_ok(lean_int_to_int(rc));
}

LEAN_EXPORT lean_obj_res lean_sudo_pam_authenticate(b_lean_obj_arg h) {
    return pam_call(h, pamfn.authenticate, pam_data(h)->silent ? PAM_SILENT : 0, true);
}

LEAN_EXPORT lean_obj_res lean_sudo_pam_acct_mgmt(b_lean_obj_arg h) {
    return pam_call(h, pamfn.acct_mgmt, PAM_SILENT, false);
}

LEAN_EXPORT lean_obj_res lean_sudo_pam_chauthtok(b_lean_obj_arg h) {
    return pam_call(h, pamfn.chauthtok, PAM_CHANGE_EXPIRED_AUTHTOK, false);
}

LEAN_EXPORT lean_obj_res lean_sudo_pam_setcred(b_lean_obj_arg h, uint8_t establish) {
    return pam_call(h, pamfn.setcred,
                    establish ? PAM_REINITIALIZE_CRED : (PAM_DELETE_CRED | PAM_SILENT), false);
}

LEAN_EXPORT lean_obj_res lean_sudo_pam_open_session(b_lean_obj_arg h) {
    return pam_call(h, pamfn.open_session, pam_data(h)->session_silent ? PAM_SILENT : 0, false);
}

LEAN_EXPORT lean_obj_res lean_sudo_pam_close_session(b_lean_obj_arg h) {
    return pam_call(h, pamfn.close_session, PAM_SILENT, false);
}

LEAN_EXPORT lean_obj_res lean_sudo_pam_set_user(b_lean_obj_arg h, b_lean_obj_arg user) {
    sudo_pam_t *st = pam_data(h);
    if (st->ended) return ls_error("PAM handle already ended");
    const char *u = ls_cstr(user);
    if (!u) return ls_error(NUL_ARG_ERROR);
    int rc = pamfn.set_item(st->pamh, PAM_USER, u);
    st->last_status = rc;
    return ls_ok(lean_int_to_int(rc));
}

/* pamGetEnv : PamHandle → IO (Array (String × String)); invalid entries dropped */
LEAN_EXPORT lean_obj_res lean_sudo_pam_getenv(b_lean_obj_arg h) {
    sudo_pam_t *st = pam_data(h);
    if (st->ended) return ls_error("PAM handle already ended");
    lean_object *arr = lean_mk_empty_array();
    char **env = pamfn.getenvlist(st->pamh);
    if (!env) return ls_ok(arr);
    for (char **e = env; *e; e++) {
        arr = push_env_pair(arr, *e, false);
        explicit_bzero(*e, strlen(*e));
        free(*e);
    }
    free(env);
    return ls_ok(arr);
}

/* Borrowed Int -> C int; false if out of range. */
static bool int_arg(b_lean_obj_arg i, int *out) {
    if (!lean_is_scalar(i)) return false;
    int64_t v = lean_scalar_to_int64(i);
    if (v < INT_MIN || v > INT_MAX) return false;
    *out = (int)v;
    return true;
}

LEAN_EXPORT lean_obj_res lean_sudo_pam_strerror(b_lean_obj_arg h, b_lean_obj_arg code) {
    sudo_pam_t *st = pam_data(h);
    int c;
    if (!int_arg(code, &c)) return ls_ok(lean_mk_string("Unknown PAM error"));
    const char *m = pamfn.strerror(st->ended ? NULL : st->pamh, c);
    return ls_ok(mk_str_lossy(m ? m : "Unknown PAM error"));
}

LEAN_EXPORT lean_obj_res lean_sudo_pam_end(b_lean_obj_arg h, b_lean_obj_arg status) {
    sudo_pam_t *st = pam_data(h);
    if (st->ended) return ls_ok(lean_box(0));
    int s;
    if (!int_arg(status, &s)) s = st->last_status;
    pamfn.end(st->pamh, s);
    st->ended = true;
    st->pamh = NULL;
    return ls_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res lean_sudo_pam_last_conv_error(b_lean_obj_arg h) {
    const char *m = conv_error_message(pam_data(h)->conv_error);
    return ls_ok(m ? mk_some(lean_mk_string(m)) : mk_none());
}
