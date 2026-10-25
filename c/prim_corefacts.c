#include "shim.h"
#include <dirent.h>
#include <errno.h>
#include <fcntl.h>
#include <grp.h>
#include <limits.h>
#include <locale.h>
#include <pwd.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <time.h>
#include <unistd.h>

extern char **environ;


static lean_object *bytes(const char *s, size_t n) {
    lean_object *a = lean_alloc_sarray(1, n, n);
    if (n) memcpy(lean_sarray_cptr(a), s, n);
    return a;
}
static lean_object *text(const char *s) { return bytes(s ? s : "", s ? strlen(s) : 0); }
static lean_object *some(lean_object *v) {
    lean_object *o = lean_alloc_ctor(1, 1, 0);
    lean_ctor_set(o, 0, v);
    return o;
}
static lean_object *number(int64_t n) { return lean_int64_to_int(n); }
static lean_object *result(int64_t n) { return ls_ok(number(n)); }
static lean_object *stat_value(const struct stat *s) {
    lean_object *a = lean_mk_empty_array_with_capacity(lean_box(7));
    uint64_t fields[] = {s->st_dev, s->st_ino, s->st_mode,
        s->st_uid, s->st_gid, 0, s->st_rdev};
    for (size_t i = 0; i < 7; i++)
        a = lean_array_push(a, i == 5 ? number(s->st_size) :
            lean_nat_to_int(lean_uint64_to_nat(fields[i])));
    return a;
}
LEAN_EXPORT lean_obj_res lean_cf_decode_lossy(b_lean_obj_arg input) {
    return lean_mk_string_from_bytes(
        (const char *)lean_sarray_cptr(input), lean_sarray_size(input));
}
LEAN_EXPORT lean_obj_res lean_cf_strerror(uint32_t e) {
    char buffer[256];
    return ls_ok(lean_mk_string(strerror_r((int)e, buffer, sizeof buffer)));
}
LEAN_EXPORT lean_obj_res lean_cf_setuid(uint32_t uid) {
    int r = setuid((uid_t)uid);
    return result(r < 0 ? -errno : r);
}
LEAN_EXPORT lean_obj_res lean_cf_shell_begin(void) { setusershell(); return ls_ok(lean_box(0)); }
LEAN_EXPORT lean_obj_res lean_cf_shell_end(void) { endusershell(); return ls_ok(lean_box(0)); }
LEAN_EXPORT lean_obj_res lean_cf_shell_next(void) {
    const char *s = getusershell();
    return ls_ok(s ? some(text(s)) : lean_box(0));
}
LEAN_EXPORT lean_obj_res lean_cf_groups(uint32_t capacity) {
    gid_t *g = capacity ? malloc((size_t)capacity * sizeof(gid_t)) : NULL;
    if (capacity && !g) return ls_ok(ls_pair(number(-ENOMEM), lean_mk_empty_array()));
    int r = getgroups((int)capacity, g);
    int e = errno;
    lean_object *a = lean_mk_empty_array_with_capacity(
        lean_box(r > 0 && capacity ? (size_t)r : 0));
    if (r > 0 && capacity)
        for (int i = 0; i < r; i++)
            a = lean_array_push(a, lean_uint64_to_nat(g[i]));
    free(g);
    return ls_ok(ls_pair(number(r < 0 ? -e : r), a));
}
LEAN_EXPORT lean_obj_res lean_cf_sysconf(uint32_t selector) {
    return result(sysconf((int)selector));
}
static lean_object *passwd_result(int rc, const struct passwd *p) {
    lean_object *strings = lean_mk_empty_array_with_capacity(lean_box(4));
    lean_object *ids = lean_mk_empty_array_with_capacity(lean_box(2));
    if (p) {
        if (p->pw_name) strings = lean_array_push(strings, text(p->pw_name));
        strings = lean_array_push(strings, text(p->pw_gecos));
        strings = lean_array_push(strings, text(p->pw_dir));
        strings = lean_array_push(strings, text(p->pw_shell));
        ids = lean_array_push(ids, lean_uint64_to_nat(p->pw_uid));
        ids = lean_array_push(ids, lean_uint64_to_nat(p->pw_gid));
    }
    return ls_ok(ls_pair(number(rc), ls_pair(strings, ids)));
}
#define PW_LOOKUP(symbol, call) \
LEAN_EXPORT lean_obj_res symbol(b_lean_obj_arg name, uint32_t uid, uint32_t size) { \
    (void)name; (void)uid; \
    char *buffer = malloc(size); \
    if (!buffer) return passwd_result(ENOMEM, NULL); \
    struct passwd pw, *p = NULL; \
    int rc = call; \
    lean_object *out = passwd_result(rc, p); \
    free(buffer); \
    return out; \
}
PW_LOOKUP(lean_cf_pwnam, getpwnam_r(lean_string_cstr(name), &pw, buffer, size, &p))
PW_LOOKUP(lean_cf_pwuid, getpwuid_r((uid_t)uid, &pw, buffer, size, &p))
static lean_object *group_result(int rc, const struct group *g) {
    lean_object *strings = lean_mk_empty_array();
    lean_object *ids = lean_mk_empty_array();
    if (g) {
        if (g->gr_name) strings = lean_array_push(strings, text(g->gr_name));
        ids = lean_array_push(ids, lean_uint64_to_nat(g->gr_gid));
    }
    return ls_ok(ls_pair(number(rc), ls_pair(strings, ids)));
}
#define GR_LOOKUP(symbol, call) \
LEAN_EXPORT lean_obj_res symbol(b_lean_obj_arg name, uint32_t gid, uint32_t size) { \
    (void)name; (void)gid; \
    char *buffer = malloc(size); \
    if (!buffer) return group_result(ENOMEM, NULL); \
    struct group gr, *g = NULL; \
    int rc = call; \
    lean_object *out = group_result(rc, g); \
    free(buffer); \
    return out; \
}
GR_LOOKUP(lean_cf_grnam, getgrnam_r(lean_string_cstr(name), &gr, buffer, size, &g))
GR_LOOKUP(lean_cf_grgid, getgrgid_r((gid_t)gid, &gr, buffer, size, &g))
LEAN_EXPORT lean_obj_res lean_cf_grouplist(b_lean_obj_arg user, uint32_t gid, uint32_t capacity) {
    gid_t *g = malloc((size_t)capacity * sizeof(gid_t));
    if (!g) return ls_ok(ls_pair(number(-ENOMEM), ls_pair(number(0), lean_mk_empty_array())));
    int count = (int)capacity;
    int rc = getgrouplist(lean_string_cstr(user), (gid_t)gid, g, &count);
    lean_object *a = lean_mk_empty_array();
    if (rc >= 0)
        for (int i = 0; i < count && i < (int)capacity; i++)
            a = lean_array_push(a, lean_uint64_to_nat(g[i]));
    free(g);
    return ls_ok(ls_pair(number(rc), ls_pair(number(count), a)));
}
LEAN_EXPORT lean_obj_res lean_cf_hostname(void) {
    char b[HOST_NAME_MAX + 2] = {0};
    int r = gethostname(b, HOST_NAME_MAX + 1);
    return ls_ok(ls_pair(number(r < 0 ? -errno : 0), text(b)));
}
LEAN_EXPORT lean_obj_res lean_cf_ttyname(uint32_t fd) {
    char b[PATH_MAX] = {0};
    int r = ttyname_r((int)fd, b, sizeof b);
    b[sizeof b - 1] = 0;
    return ls_ok(r ? lean_box(0) : some(text(b)));
}
LEAN_EXPORT lean_obj_res lean_cf_environment(void) {
    return ls_ok(lean_box_usize((size_t)environ));
}
LEAN_EXPORT lean_obj_res lean_cf_environment_entry(size_t cursor) {
    char **p = (char **)cursor;
    return ls_ok(p && *p ? some(text(*p)) : lean_box(0));
}
LEAN_EXPORT lean_obj_res lean_cf_getenv(b_lean_obj_arg name) {
    const char *p = getenv(lean_string_cstr(name));
    return ls_ok(p ? some(text(p)) : lean_box(0));
}
LEAN_EXPORT lean_obj_res lean_cf_unsetenv(b_lean_obj_arg name) {
    int r = unsetenv(lean_string_cstr(name));
    return result(r < 0 ? -errno : r);
}
LEAN_EXPORT lean_obj_res lean_cf_tzset(void) { tzset(); return ls_ok(lean_box(0)); }
LEAN_EXPORT lean_obj_res lean_cf_setlocale(void) {
    setlocale(LC_ALL, "");
    return ls_ok(lean_box(0));
}
#define STAT_WRAPPER(symbol, call, arg) \
LEAN_EXPORT lean_obj_res symbol(arg) { \
    struct stat s; \
    int r = call; \
    int e = errno; \
    return ls_ok(ls_pair(number(r < 0 ? -e : 0), r < 0 ? lean_mk_empty_array() : stat_value(&s))); \
}
STAT_WRAPPER(lean_cf_stat, stat(lean_string_cstr(path), &s), b_lean_obj_arg path)
STAT_WRAPPER(lean_cf_lstat, lstat(lean_string_cstr(path), &s), b_lean_obj_arg path)
STAT_WRAPPER(lean_cf_fstat, fstat((int)fd, &s), uint32_t fd)
LEAN_EXPORT lean_obj_res lean_cf_realpath(b_lean_obj_arg path) {
    char *p = realpath(lean_string_cstr(path), NULL);
    lean_object *o = p ? some(text(p)) : lean_box(0);
    free(p);
    return ls_ok(o);
}
LEAN_EXPORT lean_obj_res lean_cf_access(b_lean_obj_arg path, uint32_t mode) {
    int r = access(lean_string_cstr(path), (int)mode);
    return result(r < 0 ? -errno : r);
}
LEAN_EXPORT lean_obj_res lean_cf_open(b_lean_obj_arg path, uint32_t flags) {
    int r = open(lean_string_cstr(path), (int)flags);
    return result(r < 0 ? -errno : r);
}
LEAN_EXPORT lean_obj_res lean_cf_close(uint32_t fd) {
    int r = close((int)fd);
    return result(r < 0 ? -errno : r);
}
LEAN_EXPORT lean_obj_res lean_cf_dup(uint32_t fd) {
    int r = fcntl((int)fd, F_DUPFD_CLOEXEC, 3);
    return result(r < 0 ? -errno : r);
}
LEAN_EXPORT lean_obj_res lean_cf_read(uint32_t fd, uint32_t size) {
    lean_object *buffer = lean_alloc_sarray(1, 0, size);
    ssize_t r = read((int)fd, lean_sarray_cptr(buffer), size);
    int e = errno;
    if (r > 0) lean_sarray_set_size(buffer, (size_t)r);
    return ls_ok(ls_pair(number(r < 0 ? -e : r), buffer));
}
LEAN_EXPORT lean_obj_res lean_cf_fdopendir(uint32_t fd) {
    DIR *d = fdopendir((int)fd);
    return ls_ok(ls_pair(number(d ? 0 : -errno), lean_box_usize((size_t)d)));
}
LEAN_EXPORT lean_obj_res lean_cf_readdir(size_t handle) {
    errno = 0;
    struct dirent *d = readdir((DIR *)handle);
    int e = errno;
    return ls_ok(ls_pair(number(d ? 0 : -e), d ? some(text(d->d_name)) : lean_box(0)));
}
LEAN_EXPORT lean_obj_res lean_cf_closedir(size_t handle) {
    int r = closedir((DIR *)handle);
    return result(r < 0 ? -errno : r);
}
LEAN_EXPORT lean_obj_res lean_cf_getcwd(void) {
    char *p = getcwd(NULL, 0);
    int e = errno;
    lean_object *o = ls_pair(number(p ? 0 : -e), text(p));
    free(p);
    return ls_ok(o);
}
LEAN_EXPORT lean_obj_res lean_cf_write(uint32_t fd, b_lean_obj_arg bytes_arg, size_t offset) {
    if (offset > lean_sarray_size(bytes_arg)) return result(-EINVAL);
    ssize_t r = write((int)fd, lean_sarray_cptr(bytes_arg) + offset,
        lean_sarray_size(bytes_arg) - offset);
    return result(r < 0 ? -errno : r);
}
