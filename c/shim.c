#include "shim.h"
#include <dlfcn.h>
#include <errno.h>
#include <fcntl.h>
#include <grp.h>
#include <limits.h>
#include <stdarg.h>
#include <stdio.h>
#include <sys/fsuid.h>
#include <sys/socket.h>
#include <sys/syscall.h>
#include <time.h>
#include <unistd.h>

lean_obj_res ls_errorf(const char *format, ...) {
    char buffer[1024];
    va_list args;
    va_start(args, format);
    vsnprintf(buffer, sizeof buffer, format, args);
    va_end(args);
    return ls_error(buffer);
}
lean_obj_res ls_errno(int error) {
    char buffer[256];
    return ls_error(strerror_r(error, buffer, sizeof buffer));
}
bool ls_utf8_valid(const char *str, size_t n) {
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
        if (n - i - 1 < need || s[i + 1] < lo || s[i + 1] > hi) return false;
        for (size_t k = 2; k <= need; k++)
            if ((s[i + k] & 0xC0) != 0x80) return false;
        i += need + 1;
    }
    return true;
}
lean_object *ls_string_n(const char *s, size_t n) {
    return ls_utf8_valid(s, n) ? lean_mk_string_from_bytes_unchecked(s, n) : NULL;
}
lean_object *ls_string(const char *s) {
    return s ? ls_string_n(s, strlen(s)) : NULL;
}
void ls_strv_free(char **v) {
    if (v) {
        for (size_t i = 0; v[i]; i++) free(v[i]);
        free(v);
    }
}
char **ls_strv(b_lean_obj_arg array, bool copy) {
    size_t n = lean_array_size(array);
    char **v = calloc(n + 1, sizeof(*v));
    if (!v) return NULL;
    for (size_t i = 0; i < n; i++) {
        b_lean_obj_arg value = lean_array_get_core(array, i);
        const char *s = copy ? ls_cstr(value) : lean_string_cstr(value);
        if (!s) errno = EINVAL;
        else if ((v[i] = copy ? strdup(s) : (char *)s)) continue;
        if (copy) ls_strv_free(v); else free(v);
        return NULL;
    }
    return v;
}
size_t ls_strv_len(char *const *v) {
    size_t n = 0;
    if (v) while (v[n]) n++;
    return n;
}
int ls_transfer(int fd, void *buffer, size_t size, int sending) {
    unsigned char *p = buffer;
    while (size) {
        ssize_t n = sending ? send(fd, p, size, MSG_NOSIGNAL) : read(fd, p, size);
        if (n < 0 && errno == EINTR) continue;
        if (n < 0) return -1;
        if (!n) { errno = EIO; return -1; }
        p += n;
        size -= (size_t)n;
    }
    return 0;
}
int ls_write_all(int fd, const void *buffer, size_t size) {
    const char *p = buffer;
    while (size) {
        ssize_t n = write(fd, p, size);
        if (n < 0 && errno == EINTR) continue;
        if (n <= 0) { if (!n) errno = EIO; return -1; }
        p += n;
        size -= (size_t)n;
    }
    return 0;
}
int64_t ls_mono_ms(void) {
    struct timespec ts;
    if (clock_gettime(CLOCK_MONOTONIC, &ts)) return -1;
    return (int64_t)ts.tv_sec * 1000 + ts.tv_nsec / 1000000;
}
int ls_close_from(int fd) {
    if (syscall(SYS_close_range, (unsigned)fd, UINT_MAX, 0) == 0) return 0;
    long maxfd = sysconf(_SC_OPEN_MAX);
    if (maxfd < 0) return -1;
    for (; fd < maxfd; fd++) close(fd);
    return 0;
}
int ls_compare_gid(const void *a, const void *b) {
    gid_t x = *(const gid_t *)a, y = *(const gid_t *)b;
    return (x > y) - (x < y);
}
/* Callers sort groups and allocate verification storage before fork. Compare the
 * complete multiset, including duplicates, and verify filesystem/saved IDs too. */
int ls_drop_credentials(uid_t uid, gid_t gid, const gid_t *groups, size_t n, gid_t *verify) {
    uid_t ruid, euid, suid;
    gid_t rgid, egid, sgid;
    if (setgroups(n, groups) || setresgid(gid, gid, gid) || setresuid(uid, uid, uid) ||
        getresuid(&ruid, &euid, &suid) || getresgid(&rgid, &egid, &sgid)) return -1;
    if (ruid != uid || euid != uid || suid != uid ||
        rgid != gid || egid != gid || sgid != gid ||
        (uid_t)setfsuid((uid_t)-1) != uid || (gid_t)setfsgid((gid_t)-1) != gid ||
        getgroups(0, NULL) != (int)n) goto mismatch;
    if (n && (getgroups((int)n, verify) != (int)n ||
        memcmp(groups, verify, n * sizeof(*groups)))) goto mismatch;
    if (uid != 0 && setuid(0) != -1) goto mismatch;
    return 0;
mismatch:
    errno = EPERM;
    return -1;
}
bool ls_trace_supported(void) {
#if defined(__aarch64__) || defined(__x86_64__)
    int fd = open("/proc/sys/kernel/seccomp/actions_avail", O_RDONLY | O_CLOEXEC);
    if (fd < 0) return false;
    char buf[512];
    size_t used = 0;
    bool complete = false;
    while (used < sizeof buf - 1) {
        ssize_t n = read(fd, buf + used, sizeof buf - 1 - used);
        if (n < 0 && errno == EINTR) continue;
        if (n <= 0) { complete = n == 0; break; }
        used += (size_t)n;
    }
    close(fd);
    if (!complete) return false;
    buf[used] = 0;
    char *save = NULL;
    for (char *token = strtok_r(buf, " \t\r\n", &save); token;
            token = strtok_r(NULL, " \t\r\n", &save)) {
        if (!strcmp(token, "trap")) return true;
    }
    return false;
#else
    return false;
#endif
}
const char *ls_dlsyms(void *handle, const struct ls_symbol *symbols, size_t n) {
    for (size_t i = 0; i < n; i++) {
        void *symbol = dlsym(handle, symbols[i].name);
        if (!symbol) return symbols[i].name;
        memcpy(symbols[i].slot, &symbol, sizeof symbol);
    }
    return NULL;
}
