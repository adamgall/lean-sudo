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
#include <lean/lean.h>

#include <dirent.h>
#include <dlfcn.h>
#include <errno.h>
#include <fcntl.h>
#include <grp.h>
#include <limits.h>
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
#include <termios.h>
#include <time.h>
#include <unistd.h>

extern char **environ;

/* ------------------------------------------------------------------------- */
/* Helpers                                                                    */
/* ------------------------------------------------------------------------- */

static lean_obj_res io_ok(lean_obj_arg v) { return lean_io_result_mk_ok(v); }

static lean_obj_res io_err(const char *msg) {
    return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(msg)));
}

__attribute__((format(printf, 1, 2)))
static lean_obj_res io_errf(const char *fmt, ...) {
    char buf[1024];
    va_list ap;
    va_start(ap, fmt);
    vsnprintf(buf, sizeof buf, fmt, ap);
    va_end(ap);
    return io_err(buf);
}

static const char *errstr(int e, char *buf, size_t n) {
    /* GNU strerror_r (we compile with -D_GNU_SOURCE) */
    return strerror_r(e, buf, n);
}

static lean_obj_res io_errno(int e) {
    char buf[256];
    return io_err(errstr(e, buf, sizeof buf));
}

static lean_obj_res io_errno_path(const char *what, const char *path, int e) {
    char buf[256];
    return io_errf("%s %s: %s", what, path, errstr(e, buf, sizeof buf));
}

/* Strict UTF-8 validation (same acceptance as Lean's `String.validateUTF8`):
 * no overlongs, no surrogates, nothing above U+10FFFF. */
static bool utf8_valid(const char *str, size_t n) {
    const unsigned char *s = (const unsigned char *)str;
    size_t i = 0;
    while (i < n) {
        unsigned c = s[i];
        size_t need;
        unsigned lo = 0x80, hi = 0xBF;
        if (c < 0x80) { i++; continue; }
        else if (c >= 0xC2 && c <= 0xDF) need = 1;
        else if (c == 0xE0) { need = 2; lo = 0xA0; }
        else if ((c >= 0xE1 && c <= 0xEC) || c == 0xEE || c == 0xEF) need = 2;
        else if (c == 0xED) { need = 2; hi = 0x9F; }
        else if (c == 0xF0) { need = 3; lo = 0x90; }
        else if (c >= 0xF1 && c <= 0xF3) need = 3;
        else if (c == 0xF4) { need = 3; hi = 0x8F; }
        else return false;
        if (n - i - 1 < need) return false;
        if (s[i + 1] < lo || s[i + 1] > hi) return false;
        for (size_t k = 2; k <= need; k++)
            if ((s[i + k] & 0xC0) != 0x80) return false;
        i += need + 1;
    }
    return true;
}

/* Make a Lean string from n bytes; NULL if not valid UTF-8. */
static lean_object *mk_str_n(const char *s, size_t n) {
    if (!utf8_valid(s, n)) return NULL;
    return lean_mk_string_from_bytes_unchecked(s, n);
}

static lean_object *mk_str(const char *s) { return mk_str_n(s, strlen(s)); }

/* Lossy variant for informational text (PAM messages etc.). */
static lean_object *mk_str_lossy(const char *s) { return lean_mk_string_from_bytes(s, strlen(s)); }

/* Borrowed Lean string -> C string, or NULL if it contains a NUL byte. */
static const char *cstr_arg(b_lean_obj_arg s) {
    const char *c = lean_string_cstr(s);
    if (strlen(c) != lean_string_size(s) - 1) return NULL;
    return c;
}

static lean_obj_res mk_some(lean_obj_arg v) {
    lean_object *o = lean_alloc_ctor(1, 1, 0);
    lean_ctor_set(o, 0, v);
    return o;
}

static lean_obj_res mk_none(void) { return lean_box(0); }

static lean_obj_res mk_pair(lean_obj_arg a, lean_obj_arg b) {
    lean_object *o = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(o, 0, a);
    lean_ctor_set(o, 1, b);
    return o;
}

static lean_obj_res mk_nat(uint64_t v) { return lean_uint64_to_nat(v); }

static int write_all(int fd, const char *buf, size_t n) {
    while (n > 0) {
        ssize_t k = write(fd, buf, n);
        if (k < 0) {
            if (errno == EINTR) continue;
            return -1;
        }
        buf += k;
        n -= (size_t)k;
    }
    return 0;
}

static int write_str(int fd, const char *s) { return write_all(fd, s, strlen(s)); }

#define NUL_ARG_ERROR "argument contains a NUL byte"

/* ------------------------------------------------------------------------- */
/* Ids                                                                        */
/* ------------------------------------------------------------------------- */

LEAN_EXPORT lean_obj_res lean_sudo_getuid(void) { return io_ok(mk_nat(getuid())); }
LEAN_EXPORT lean_obj_res lean_sudo_geteuid(void) { return io_ok(mk_nat(geteuid())); }
LEAN_EXPORT lean_obj_res lean_sudo_getgid(void) { return io_ok(mk_nat(getgid())); }
LEAN_EXPORT lean_obj_res lean_sudo_getegid(void) { return io_ok(mk_nat(getegid())); }

static lean_obj_res gid_array(const gid_t *g, size_t n) {
    lean_object *arr = lean_mk_empty_array_with_capacity(lean_box(n));
    for (size_t i = 0; i < n; i++) arr = lean_array_push(arr, mk_nat(g[i]));
    return arr;
}

/* getgroups : IO (Array Nat) */
LEAN_EXPORT lean_obj_res lean_sudo_getgroups(void) {
    for (int attempt = 0; attempt < 8; attempt++) {
        int n = getgroups(0, NULL);
        if (n < 0) return io_errno(errno);
        gid_t *g = malloc(sizeof(gid_t) * ((size_t)n + 1));
        if (!g) return io_errno(ENOMEM);
        int m = getgroups(n + 1, g);
        if (m < 0) {
            int e = errno;
            free(g);
            if (e == EINVAL) continue; /* group list grew between calls */
            return io_errno(e);
        }
        lean_object *arr = gid_array(g, (size_t)m);
        free(g);
        return io_ok(arr);
    }
    return io_errno(EINVAL);
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
        if (!buf) return io_errno(ENOMEM);
        struct passwd pw, *res = NULL;
        int rc = name ? getpwnam_r(name, &pw, buf, sz, &res) : getpwuid_r(uid, &pw, buf, sz, &res);
        if (rc == ERANGE && sz < NSS_BUF_MAX) { free(buf); sz *= 2; continue; }
        if (rc == EINTR) { free(buf); continue; }
        if (res == NULL) {
            free(buf);
            if (nss_not_found(rc)) return io_ok(mk_none());
            return io_errno(rc);
        }
        lean_object *pname = mk_str(pw.pw_name);
        lean_object *home = mk_str(pw.pw_dir ? pw.pw_dir : "");
        lean_object *shell = mk_str(pw.pw_shell ? pw.pw_shell : "");
        lean_object *gecos = mk_str_lossy(pw.pw_gecos ? pw.pw_gecos : "");
        uid_t pu = pw.pw_uid;
        gid_t pg = pw.pw_gid;
        free(buf);
        if (!pname || !home || !shell) {
            if (pname) lean_dec(pname);
            if (home) lean_dec(home);
            if (shell) lean_dec(shell);
            lean_dec(gecos);
            return io_err("passwd entry is not valid UTF-8");
        }
        lean_object *o = lean_alloc_ctor(0, 6, 0);
        lean_ctor_set(o, 0, pname);
        lean_ctor_set(o, 1, mk_nat(pu));
        lean_ctor_set(o, 2, mk_nat(pg));
        lean_ctor_set(o, 3, gecos);
        lean_ctor_set(o, 4, home);
        lean_ctor_set(o, 5, shell);
        return io_ok(mk_some(o));
    }
}

LEAN_EXPORT lean_obj_res lean_sudo_getpwnam(b_lean_obj_arg name) {
    const char *n = cstr_arg(name);
    if (!n) return io_ok(mk_none());
    return pw_lookup(n, 0);
}

LEAN_EXPORT lean_obj_res lean_sudo_getpwuid(uint32_t uid) { return pw_lookup(NULL, (uid_t)uid); }

/* Returns Option (String × Nat) */
static lean_obj_res gr_lookup(const char *name, gid_t gid) {
    size_t sz = nss_initial(_SC_GETGR_R_SIZE_MAX);
    for (;;) {
        char *buf = malloc(sz);
        if (!buf) return io_errno(ENOMEM);
        struct group gr, *res = NULL;
        int rc = name ? getgrnam_r(name, &gr, buf, sz, &res) : getgrgid_r(gid, &gr, buf, sz, &res);
        if (rc == ERANGE && sz < NSS_BUF_MAX) { free(buf); sz *= 2; continue; }
        if (rc == EINTR) { free(buf); continue; }
        if (res == NULL) {
            free(buf);
            if (nss_not_found(rc)) return io_ok(mk_none());
            return io_errno(rc);
        }
        lean_object *gname = mk_str(gr.gr_name);
        gid_t g = gr.gr_gid;
        free(buf);
        if (!gname) return io_err("group entry is not valid UTF-8");
        return io_ok(mk_some(mk_pair(gname, mk_nat(g))));
    }
}

LEAN_EXPORT lean_obj_res lean_sudo_getgrnam(b_lean_obj_arg name) {
    const char *n = cstr_arg(name);
    if (!n) return io_ok(mk_none());
    return gr_lookup(n, 0);
}

LEAN_EXPORT lean_obj_res lean_sudo_getgrgid(uint32_t gid) { return gr_lookup(NULL, (gid_t)gid); }

/* getgrouplist : String → UInt32 → IO (Array Nat) */
LEAN_EXPORT lean_obj_res lean_sudo_getgrouplist(b_lean_obj_arg user, uint32_t gid) {
    const char *u = cstr_arg(user);
    if (!u) return io_err(NUL_ARG_ERROR);
    int n = 64;
    for (;;) {
        gid_t *g = malloc(sizeof(gid_t) * (size_t)n);
        if (!g) return io_errno(ENOMEM);
        int cnt = n;
        int rc = getgrouplist(u, (gid_t)gid, g, &cnt);
        if (rc >= 0) {
            if (cnt > n) cnt = n;
            lean_object *arr = gid_array(g, (size_t)cnt);
            free(g);
            return io_ok(arr);
        }
        free(g);
        int next = cnt > n ? cnt : n * 2;
        if (next > (1 << 20)) return io_err("getgrouplist: too many groups");
        n = next;
    }
}

/* ------------------------------------------------------------------------- */
/* host / tty / environ                                                       */
/* ------------------------------------------------------------------------- */

LEAN_EXPORT lean_obj_res lean_sudo_gethostname(void) {
    char buf[HOST_NAME_MAX + 2];
    memset(buf, 0, sizeof buf);
    if (gethostname(buf, HOST_NAME_MAX + 1) != 0) return io_errno(errno);
    buf[HOST_NAME_MAX + 1] = '\0';
    lean_object *s = mk_str(buf);
    if (!s) return io_err("host name is not valid UTF-8");
    return io_ok(s);
}

LEAN_EXPORT lean_obj_res lean_sudo_isatty(uint32_t fd) {
    return io_ok(lean_box(isatty((int)fd) ? 1 : 0));
}

LEAN_EXPORT lean_obj_res lean_sudo_ttyname(uint32_t fd) {
    char buf[PATH_MAX];
    if (ttyname_r((int)fd, buf, sizeof buf) != 0) return io_ok(mk_none());
    buf[sizeof buf - 1] = '\0';
    lean_object *s = mk_str(buf);
    return io_ok(s ? mk_some(s) : mk_none());
}

/* environ : IO (Array (String × String)); drops entries without '=' or not UTF-8 */
LEAN_EXPORT lean_obj_res lean_sudo_environ(void) {
    lean_object *arr = lean_mk_empty_array();
    for (char **e = environ; e && *e; e++) {
        const char *eq = strchr(*e, '=');
        if (!eq) continue;
        size_t klen = (size_t)(eq - *e);
        const char *v = eq + 1;
        size_t vlen = strlen(v);
        if (!utf8_valid(*e, klen) || !utf8_valid(v, vlen)) continue;
        lean_object *k = lean_mk_string_from_bytes_unchecked(*e, klen);
        lean_object *val = lean_mk_string_from_bytes_unchecked(v, vlen);
        arr = lean_array_push(arr, mk_pair(k, val));
    }
    return io_ok(arr);
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
    const char *p = cstr_arg(path);
    struct stat st;
    if (!p || stat(p, &st) != 0) return io_ok(mk_none());
    return io_ok(mk_some(mk_filestat(&st)));
}

LEAN_EXPORT lean_obj_res lean_sudo_lstat(b_lean_obj_arg path) {
    const char *p = cstr_arg(path);
    struct stat st;
    if (!p || lstat(p, &st) != 0) return io_ok(mk_none());
    return io_ok(mk_some(mk_filestat(&st)));
}

LEAN_EXPORT lean_obj_res lean_sudo_realpath(b_lean_obj_arg path) {
    const char *p = cstr_arg(path);
    if (!p) return io_ok(mk_none());
    char *r = realpath(p, NULL);
    if (!r) return io_ok(mk_none());
    lean_object *s = mk_str(r);
    free(r);
    return io_ok(s ? mk_some(s) : mk_none());
}

LEAN_EXPORT lean_obj_res lean_sudo_access(b_lean_obj_arg path, uint32_t mode) {
    const char *p = cstr_arg(path);
    if (!p) return io_ok(lean_box(0));
    return io_ok(lean_box(access(p, (int)mode) == 0 ? 1 : 0));
}

#define READ_CAP ((size_t)16 << 20)

/* readFileNoFollow : String → IO (FileStat × String) */
LEAN_EXPORT lean_obj_res lean_sudo_read_file_nofollow(b_lean_obj_arg path) {
    const char *p = cstr_arg(path);
    if (!p) return io_err(NUL_ARG_ERROR);
    int fd;
    do {
        fd = open(p, O_RDONLY | O_NOFOLLOW | O_CLOEXEC | O_NONBLOCK | O_NOCTTY);
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
        return io_errf("%s is not a regular file", p);
    }
    if (st.st_size < 0 || (size_t)st.st_size > READ_CAP) {
        close(fd);
        return io_errf("%s: file too large", p);
    }
    size_t cap = (size_t)st.st_size + 1; /* +1 to detect growth */
    char *buf = malloc(cap);
    if (!buf) { close(fd); return io_errno(ENOMEM); }
    size_t len = 0;
    for (;;) {
        if (len == cap) {
            if (cap > READ_CAP) {
                free(buf);
                close(fd);
                return io_errf("%s: file too large", p);
            }
            size_t ncap = cap * 2 > READ_CAP + 1 ? READ_CAP + 1 : cap * 2;
            char *nb = realloc(buf, ncap);
            if (!nb) { free(buf); close(fd); return io_errno(ENOMEM); }
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
        return io_errf("%s: file too large", p);
    }
    lean_object *s = mk_str_n(buf, len);
    free(buf);
    if (!s) return io_errf("%s: file is not valid UTF-8", p);
    return io_ok(mk_pair(mk_filestat(&st), s));
}

/* listDir : String → IO (Array String) — names excluding . and .., unsorted */
LEAN_EXPORT lean_obj_res lean_sudo_list_dir(b_lean_obj_arg path) {
    const char *p = cstr_arg(path);
    if (!p) return io_err(NUL_ARG_ERROR);
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
            return io_ok(arr);
        }
        if (strcmp(de->d_name, ".") == 0 || strcmp(de->d_name, "..") == 0) continue;
        lean_object *s = mk_str(de->d_name);
        if (!s) {
            closedir(d);
            lean_dec(arr);
            return io_errf("%s: directory entry name is not valid UTF-8", p);
        }
        arr = lean_array_push(arr, s);
    }
}

LEAN_EXPORT lean_obj_res lean_sudo_getcwd(void) {
    char *c = getcwd(NULL, 0);
    if (!c) return io_errno(errno);
    lean_object *s = mk_str(c);
    free(c);
    if (!s) return io_err("current directory is not valid UTF-8");
    return io_ok(s);
}

/* umask : UInt32 → IO UInt32 — sets the mask, returns the previous one */
LEAN_EXPORT lean_obj_res lean_sudo_umask(uint32_t mask) {
    return io_ok(lean_box_uint32((uint32_t)umask((mode_t)(mask & 07777))));
}

LEAN_EXPORT lean_obj_res lean_sudo_write_stderr(b_lean_obj_arg s) {
    if (write_all(STDERR_FILENO, lean_string_cstr(s), lean_string_size(s) - 1) != 0)
        return io_errno(errno);
    return io_ok(lean_box(0));
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
    const char *f = cstr_arg(facility), *p = cstr_arg(priority);
    if (!f || !lookup_name(facilities, f, &fac)) return io_err("unknown syslog facility");
    if (!p || !lookup_name(priorities, p, &pri)) return io_err("unknown syslog priority");
    /* A NUL in the message just truncates it, which is harmless for logging. */
    openlog("sudo", LOG_PID, fac);
    syslog(fac | pri, "%s", lean_string_cstr(msg));
    closelog();
    return io_ok(lean_box(0));
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
    const struct { const char *name; void *slot; } syms[] = {
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
    };
    for (size_t i = 0; i < sizeof syms / sizeof syms[0]; i++) {
        void *f = dlsym(h, syms[i].name);
        if (!f) {
            snprintf(pam_load_error, sizeof pam_load_error, "libpam.so.0: missing symbol %s",
                     syms[i].name);
            memset(&pamfn, 0, sizeof pamfn);
            dlclose(h);
            return;
        }
        memcpy(syms[i].slot, &f, sizeof f);
    }
    pam_loaded = true;
}

static bool pam_ensure_loaded(void) {
    pthread_once(&pam_load_once, pam_load);
    return pam_loaded;
}

LEAN_EXPORT lean_obj_res lean_sudo_pam_available(void) {
    return io_ok(lean_box(pam_ensure_loaded() ? 1 : 0));
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
    bool use_stdin, noninteractive, override, pwfeedback;
    uint32_t timeout;
    char *prompt;
    int conv_error;
} sudo_pam_t;

/* --- terminal handling during password reads --- */

static volatile sig_atomic_t tty_active;
static int tty_fd = -1;
static struct termios tty_saved, tty_noecho;

static const int tty_sigs[] = {SIGINT, SIGQUIT, SIGTERM, SIGHUP, SIGTSTP, SIGTTIN, SIGTTOU};
#define N_TTY_SIGS (sizeof tty_sigs / sizeof tty_sigs[0])
static struct sigaction tty_old_actions[N_TTY_SIGS];
static bool tty_installed[N_TTY_SIGS];

static void tty_sig_handler(int sig);

static void tty_install_one(size_t i) {
    struct sigaction sa;
    memset(&sa, 0, sizeof sa);
    sa.sa_handler = tty_sig_handler;
    sigemptyset(&sa.sa_mask);
    sa.sa_flags = 0; /* no SA_RESTART: interrupt poll/read so we re-check */
    sigaction(tty_sigs[i], &sa, NULL);
}

/* Restore the terminal, then deliver the signal with its default action. For job
 * control stops we re-arm and re-disable echo once continued. Async-signal-safe. */
static void tty_sig_handler(int sig) {
    int saved_errno = errno;
    if (tty_active) tcsetattr(tty_fd, TCSANOW, &tty_saved);
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

static int64_t monotonic_ms(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (int64_t)ts.tv_sec * 1000 + ts.tv_nsec / 1000000;
}

/* Read one line into buf (NUL-terminated, newline stripped). Returns CONV_OK or an error. */
static int read_password(sudo_pam_t *st, const char *prompt, bool echo, char *buf, size_t size) {
    int in, out, own_fd = -1;
    if (st->use_stdin) {
        in = STDIN_FILENO;
        out = STDERR_FILENO;
    } else {
        own_fd = open("/dev/tty", O_RDWR | O_NOCTTY | O_CLOEXEC);
        if (own_fd < 0) return CONV_ERR_NO_TTY;
        in = out = own_fd;
    }

    (void)write_str(out, prompt);

    bool noecho = false, feedback = false;
    struct termios saved;
    memset(&saved, 0, sizeof saved);
    if (!echo && tcgetattr(in, &saved) == 0) {
        struct termios t = saved;
        t.c_lflag &= ~(tcflag_t)(ECHO | ECHONL);
        if (st->pwfeedback) {
            t.c_lflag &= ~(tcflag_t)(ICANON | IEXTEN);
            t.c_cc[VMIN] = 1;
            t.c_cc[VTIME] = 0;
        }
        tty_fd = in;
        tty_saved = saved;
        tty_noecho = t;
        tty_install_handlers();
        int rc;
        do {
            rc = tcsetattr(in, TCSADRAIN, &t);
        } while (rc != 0 && errno == EINTR);
        if (rc == 0) {
            tty_active = 1;
            noecho = true;
            feedback = st->pwfeedback;
        } else {
            tty_restore_handlers();
        }
    }

    int64_t deadline = st->timeout > 0 ? monotonic_ms() + (int64_t)st->timeout * 1000 : 0;
    size_t n = 0;
    bool got_any = false;
    int result = CONV_OK;
    for (;;) {
        struct pollfd pfd = {.fd = in, .events = POLLIN, .revents = 0};
        int remaining = -1;
        if (deadline) {
            int64_t left = deadline - monotonic_ms();
            if (left <= 0) { result = CONV_ERR_TIMEOUT; break; }
            remaining = left > INT_MAX ? INT_MAX : (int)left;
        }
        int pr = poll(&pfd, 1, remaining);
        if (pr < 0) {
            if (errno == EINTR) continue;
            result = CONV_ERR_READ;
            break;
        }
        if (pr == 0) { result = CONV_ERR_TIMEOUT; break; }
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
        tty_restore_handlers();
        tty_fd = -1;
        explicit_bzero(&tty_saved, sizeof tty_saved);
        (void)write_str(out, "\n");
    }
    if (own_fd >= 0) close(own_fd);
    if (result != CONV_OK) explicit_bzero(buf, size);
    return result;
}

static bool is_generic_password_prompt(const char *p) {
    return p && strncmp(p, "Password", 8) == 0;
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
            bool echo = m->msg_style == PAM_PROMPT_ECHO_ON;
            const char *prompt = m->msg ? m->msg : "";
            if (!echo && (st->override || is_generic_password_prompt(m->msg))) prompt = st->prompt;
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
                (void)write_str(STDERR_FILENO, m->msg);
                (void)write_str(STDERR_FILENO, "\n");
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
    lean_obj_res res = io_errf("unable to initialize PAM: %s", msg ? msg : "unknown error");
    if (st->pamh) pamfn.end(st->pamh, rc);
    sudo_pam_free(st);
    return res;
}

/* pamStartRaw (service user : @& String) (useStdin nonInteractive : Bool) (prompt : @& String)
 *   (override pwfeedback : Bool) (timeout : UInt32) (ruser : @& String) (tty : @& Option String)
 *   : IO PamHandle */
LEAN_EXPORT lean_obj_res lean_sudo_pam_start(b_lean_obj_arg service, b_lean_obj_arg user,
                                             uint8_t use_stdin, uint8_t noninteractive,
                                             b_lean_obj_arg prompt, uint8_t override,
                                             uint8_t pwfeedback, uint32_t timeout,
                                             b_lean_obj_arg ruser, b_lean_obj_arg tty) {
    if (!pam_ensure_loaded()) return io_err(pam_load_error);
    const char *svc = cstr_arg(service), *usr = cstr_arg(user), *pr = cstr_arg(prompt),
               *ru = cstr_arg(ruser);
    const char *tt = NULL;
    if (!lean_is_scalar(tty)) {
        tt = cstr_arg(lean_ctor_get(tty, 0));
        if (!tt) return io_err(NUL_ARG_ERROR);
    }
    if (!svc || !usr || !pr || !ru) return io_err(NUL_ARG_ERROR);

    pthread_once(&pam_class_once, pam_class_init);
    sudo_pam_t *st = calloc(1, sizeof *st);
    if (!st) return io_errno(ENOMEM);
    st->prompt = strdup(pr);
    if (!st->prompt) { free(st); return io_errno(ENOMEM); }
    st->use_stdin = use_stdin;
    st->noninteractive = noninteractive;
    st->override = override;
    st->pwfeedback = pwfeedback;
    st->timeout = timeout;
    st->conv.conv = sudo_conv;
    st->conv.appdata_ptr = st;

    int rc = pamfn.start(svc, usr, &st->conv, &st->pamh);
    if (rc != PAM_SUCCESS) return pam_start_fail(st, rc);
    rc = pamfn.set_item(st->pamh, PAM_RUSER, ru);
    if (rc != PAM_SUCCESS) return pam_start_fail(st, rc);
    if (tt) {
        rc = pamfn.set_item(st->pamh, PAM_TTY, tt);
        if (rc != PAM_SUCCESS) return pam_start_fail(st, rc);
    }
    return io_ok(lean_alloc_external(pam_class, st));
}

static lean_obj_res pam_call(b_lean_obj_arg h, int (*fn)(pam_handle_t *, int), int flags) {
    sudo_pam_t *st = pam_data(h);
    if (st->ended) return io_err("PAM handle already ended");
    st->conv_error = CONV_OK;
    int rc = fn(st->pamh, flags);
    st->last_status = rc;
    return io_ok(lean_int_to_int(rc));
}

LEAN_EXPORT lean_obj_res lean_sudo_pam_authenticate(b_lean_obj_arg h) {
    return pam_call(h, pamfn.authenticate, PAM_SILENT);
}

LEAN_EXPORT lean_obj_res lean_sudo_pam_acct_mgmt(b_lean_obj_arg h) {
    return pam_call(h, pamfn.acct_mgmt, PAM_SILENT);
}

LEAN_EXPORT lean_obj_res lean_sudo_pam_chauthtok(b_lean_obj_arg h) {
    return pam_call(h, pamfn.chauthtok, PAM_CHANGE_EXPIRED_AUTHTOK);
}

LEAN_EXPORT lean_obj_res lean_sudo_pam_setcred(b_lean_obj_arg h, uint8_t establish) {
    return pam_call(h, pamfn.setcred,
                    establish ? PAM_ESTABLISH_CRED : (PAM_DELETE_CRED | PAM_SILENT));
}

LEAN_EXPORT lean_obj_res lean_sudo_pam_open_session(b_lean_obj_arg h) {
    return pam_call(h, pamfn.open_session, 0);
}

LEAN_EXPORT lean_obj_res lean_sudo_pam_close_session(b_lean_obj_arg h) {
    return pam_call(h, pamfn.close_session, PAM_SILENT);
}

LEAN_EXPORT lean_obj_res lean_sudo_pam_set_user(b_lean_obj_arg h, b_lean_obj_arg user) {
    sudo_pam_t *st = pam_data(h);
    if (st->ended) return io_err("PAM handle already ended");
    const char *u = cstr_arg(user);
    if (!u) return io_err(NUL_ARG_ERROR);
    int rc = pamfn.set_item(st->pamh, PAM_USER, u);
    st->last_status = rc;
    return io_ok(lean_int_to_int(rc));
}

/* pamGetEnv : PamHandle → IO (Array (String × String)); invalid entries dropped */
LEAN_EXPORT lean_obj_res lean_sudo_pam_getenv(b_lean_obj_arg h) {
    sudo_pam_t *st = pam_data(h);
    if (st->ended) return io_err("PAM handle already ended");
    lean_object *arr = lean_mk_empty_array();
    char **env = pamfn.getenvlist(st->pamh);
    if (!env) return io_ok(arr);
    for (char **e = env; *e; e++) {
        const char *eq = strchr(*e, '=');
        if (eq) {
            size_t klen = (size_t)(eq - *e);
            const char *v = eq + 1;
            size_t vlen = strlen(v);
            if (klen > 0 && utf8_valid(*e, klen) && utf8_valid(v, vlen)) {
                lean_object *k = lean_mk_string_from_bytes_unchecked(*e, klen);
                lean_object *val = lean_mk_string_from_bytes_unchecked(v, vlen);
                arr = lean_array_push(arr, mk_pair(k, val));
            }
        }
        explicit_bzero(*e, strlen(*e));
        free(*e);
    }
    free(env);
    return io_ok(arr);
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
    if (!int_arg(code, &c)) return io_ok(lean_mk_string("Unknown PAM error"));
    const char *m = pamfn.strerror(st->ended ? NULL : st->pamh, c);
    return io_ok(mk_str_lossy(m ? m : "Unknown PAM error"));
}

LEAN_EXPORT lean_obj_res lean_sudo_pam_end(b_lean_obj_arg h, b_lean_obj_arg status) {
    sudo_pam_t *st = pam_data(h);
    if (st->ended) return io_ok(lean_box(0));
    int s;
    if (!int_arg(status, &s)) s = st->last_status;
    pamfn.end(st->pamh, s);
    st->ended = true;
    st->pamh = NULL;
    return io_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res lean_sudo_pam_last_conv_error(b_lean_obj_arg h) {
    const char *m = conv_error_message(pam_data(h)->conv_error);
    return io_ok(m ? mk_some(lean_mk_string(m)) : mk_none());
}
