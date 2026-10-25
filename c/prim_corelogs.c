#include "shim.h"
#include <ctype.h>
#include <errno.h>
#include <fcntl.h>
#include <langinfo.h>
#include <signal.h>
#include <sys/file.h>
#include <sys/ioctl.h>
#include <sys/prctl.h>
#include <sys/random.h>
#include <sys/stat.h>
#include <sys/utsname.h>
#include <syslog.h>
#include <time.h>
#include <unistd.h>

#define CORELOGS_CONSTANT(name) \
    LEAN_EXPORT uint32_t lean_corelogs_##name(b_lean_obj_arg unit) { \
        (void)unit; return name; \
    }
CORELOGS_CONSTANT(LOG_AUTHPRIV)
CORELOGS_CONSTANT(LOG_AUTH)
CORELOGS_CONSTANT(LOG_DAEMON)
CORELOGS_CONSTANT(LOG_USER)
CORELOGS_CONSTANT(LOG_LOCAL0)
CORELOGS_CONSTANT(LOG_LOCAL1)
CORELOGS_CONSTANT(LOG_LOCAL2)
CORELOGS_CONSTANT(LOG_LOCAL3)
CORELOGS_CONSTANT(LOG_LOCAL4)
CORELOGS_CONSTANT(LOG_LOCAL5)
CORELOGS_CONSTANT(LOG_LOCAL6)
CORELOGS_CONSTANT(LOG_LOCAL7)
CORELOGS_CONSTANT(LOG_ALERT)
CORELOGS_CONSTANT(LOG_CRIT)
CORELOGS_CONSTANT(LOG_ERR)
CORELOGS_CONSTANT(LOG_WARNING)
CORELOGS_CONSTANT(LOG_NOTICE)
CORELOGS_CONSTANT(LOG_INFO)
CORELOGS_CONSTANT(LOG_DEBUG)
CORELOGS_CONSTANT(LOG_PID)
CORELOGS_CONSTANT(SIGILL)
CORELOGS_CONSTANT(SIGTRAP)
CORELOGS_CONSTANT(SIGABRT)
CORELOGS_CONSTANT(SIGBUS)
CORELOGS_CONSTANT(SIGFPE)
CORELOGS_CONSTANT(SIGUSR1)
CORELOGS_CONSTANT(SIGSEGV)
CORELOGS_CONSTANT(SIGUSR2)
CORELOGS_CONSTANT(SIGALRM)
CORELOGS_CONSTANT(SIGSTKFLT)
CORELOGS_CONSTANT(SIGURG)
CORELOGS_CONSTANT(SIGXCPU)
CORELOGS_CONSTANT(SIGXFSZ)
CORELOGS_CONSTANT(SIGVTALRM)
CORELOGS_CONSTANT(SIGPROF)
CORELOGS_CONSTANT(SIGWINCH)
CORELOGS_CONSTANT(SIGIO)
CORELOGS_CONSTANT(SIGPWR)
CORELOGS_CONSTANT(SIGSYS)
CORELOGS_CONSTANT(ABDAY_1)
CORELOGS_CONSTANT(ABDAY_2)
CORELOGS_CONSTANT(ABDAY_3)
CORELOGS_CONSTANT(ABDAY_4)
CORELOGS_CONSTANT(ABDAY_5)
CORELOGS_CONSTANT(ABDAY_6)
CORELOGS_CONSTANT(ABDAY_7)
CORELOGS_CONSTANT(DAY_1)
CORELOGS_CONSTANT(DAY_2)
CORELOGS_CONSTANT(DAY_3)
CORELOGS_CONSTANT(DAY_4)
CORELOGS_CONSTANT(DAY_5)
CORELOGS_CONSTANT(DAY_6)
CORELOGS_CONSTANT(DAY_7)
CORELOGS_CONSTANT(ABMON_1)
CORELOGS_CONSTANT(ABMON_2)
CORELOGS_CONSTANT(ABMON_3)
CORELOGS_CONSTANT(ABMON_4)
CORELOGS_CONSTANT(ABMON_5)
CORELOGS_CONSTANT(ABMON_6)
CORELOGS_CONSTANT(ABMON_7)
CORELOGS_CONSTANT(ABMON_8)
CORELOGS_CONSTANT(ABMON_9)
CORELOGS_CONSTANT(ABMON_10)
CORELOGS_CONSTANT(ABMON_11)
CORELOGS_CONSTANT(ABMON_12)
CORELOGS_CONSTANT(MON_1)
CORELOGS_CONSTANT(MON_2)
CORELOGS_CONSTANT(MON_3)
CORELOGS_CONSTANT(MON_4)
CORELOGS_CONSTANT(MON_5)
CORELOGS_CONSTANT(MON_6)
CORELOGS_CONSTANT(MON_7)
CORELOGS_CONSTANT(MON_8)
CORELOGS_CONSTANT(MON_9)
CORELOGS_CONSTANT(MON_10)
CORELOGS_CONSTANT(MON_11)
CORELOGS_CONSTANT(MON_12)
CORELOGS_CONSTANT(ALTMON_1)
CORELOGS_CONSTANT(ALTMON_2)
CORELOGS_CONSTANT(ALTMON_3)
CORELOGS_CONSTANT(ALTMON_4)
CORELOGS_CONSTANT(ALTMON_5)
CORELOGS_CONSTANT(ALTMON_6)
CORELOGS_CONSTANT(ALTMON_7)
CORELOGS_CONSTANT(ALTMON_8)
CORELOGS_CONSTANT(ALTMON_9)
CORELOGS_CONSTANT(ALTMON_10)
CORELOGS_CONSTANT(ALTMON_11)
CORELOGS_CONSTANT(ALTMON_12)
CORELOGS_CONSTANT(AM_STR)
CORELOGS_CONSTANT(PM_STR)
CORELOGS_CONSTANT(D_T_FMT)
CORELOGS_CONSTANT(D_FMT)
CORELOGS_CONSTANT(T_FMT)
CORELOGS_CONSTANT(T_FMT_AMPM)
CORELOGS_CONSTANT(ERA)
CORELOGS_CONSTANT(ERA_D_T_FMT)
CORELOGS_CONSTANT(ERA_D_FMT)
CORELOGS_CONSTANT(ERA_T_FMT)
CORELOGS_CONSTANT(ALT_DIGITS)
#undef CORELOGS_CONSTANT

#define CORELOGS_ABALTMON(number) \
    LEAN_EXPORT uint32_t lean_corelogs_ABALTMON_##number(b_lean_obj_arg unit) { \
        (void)unit; return _NL_ABALTMON_##number; \
    }
CORELOGS_ABALTMON(1)
CORELOGS_ABALTMON(2)
CORELOGS_ABALTMON(3)
CORELOGS_ABALTMON(4)
CORELOGS_ABALTMON(5)
CORELOGS_ABALTMON(6)
CORELOGS_ABALTMON(7)
CORELOGS_ABALTMON(8)
CORELOGS_ABALTMON(9)
CORELOGS_ABALTMON(10)
CORELOGS_ABALTMON(11)
CORELOGS_ABALTMON(12)
#undef CORELOGS_ABALTMON

LEAN_EXPORT lean_obj_res lean_corelogs_strerror(uint32_t error) {
    char buffer[256];
    return ls_ok(lean_mk_string(strerror_r(error, buffer, sizeof buffer)));
}

LEAN_EXPORT lean_obj_res lean_corelogs_openlog(b_lean_obj_arg ident,
        uint32_t options, uint32_t facility) {
    openlog(lean_string_cstr(ident), options, facility);
    return ls_unit();
}

LEAN_EXPORT lean_obj_res lean_corelogs_syslog_text(uint32_t priority, b_lean_obj_arg text) {
    syslog(priority, "%s", lean_string_cstr(text));
    return ls_unit();
}

LEAN_EXPORT lean_obj_res lean_corelogs_syslog_bytes(uint32_t priority, b_lean_obj_arg bytes) {
    syslog(priority, "%.*s", (int)lean_sarray_size(bytes), (const char *)lean_sarray_cptr(bytes));
    return ls_unit();
}

LEAN_EXPORT lean_obj_res lean_corelogs_closelog(void) {
    closelog();
    return ls_unit();
}

LEAN_EXPORT lean_obj_res lean_corelogs_time(void) {
    time_t now = time(NULL);
    int error = now < 0 ? errno : 0;
    return ls_ok(ls_pair(lean_box_uint32(error), lean_box_uint64((uint64_t)now)));
}

LEAN_EXPORT lean_obj_res lean_corelogs_clock(void) {
    struct timespec ts = {0};
    int rc = clock_gettime(CLOCK_REALTIME, &ts);
    int error = rc < 0 ? errno : 0;
    return ls_ok(ls_pair(lean_box_uint32(error), ls_pair(lean_box_uint64(ts.tv_sec),
        lean_box_uint64(ts.tv_nsec))));
}

#define MARSHAL_TM(tm) \
    lean_object *a = lean_mk_empty_array_with_capacity(lean_box(9)); \
    a = lean_array_push(a, lean_box_uint32((tm).tm_sec)); \
    a = lean_array_push(a, lean_box_uint32((tm).tm_min)); \
    a = lean_array_push(a, lean_box_uint32((tm).tm_hour)); \
    a = lean_array_push(a, lean_box_uint32((tm).tm_mday)); \
    a = lean_array_push(a, lean_box_uint32((tm).tm_mon)); \
    a = lean_array_push(a, lean_box_uint32((tm).tm_year)); \
    a = lean_array_push(a, lean_box_uint32((tm).tm_wday)); \
    a = lean_array_push(a, lean_box_uint32((tm).tm_yday)); \
    a = lean_array_push(a, lean_box_uint32((tm).tm_isdst)); \
    const char *zone = (tm).tm_zone; \
    size_t zone_size = zone ? strlen(zone) : 0; \
    lean_object *zone_bytes = lean_alloc_sarray(1, zone_size, zone_size); \
    if (zone_size) memcpy(lean_sarray_cptr(zone_bytes), zone, zone_size); \
    lean_object *fields = lean_alloc_ctor(0, 2, sizeof(uint64_t)); \
    lean_ctor_set(fields, 0, a); \
    lean_ctor_set(fields, 1, zone_bytes); \
    lean_ctor_set_uint64(fields, 2 * sizeof(void *), (uint64_t)(tm).tm_gmtoff); \
    lean_object *some = lean_alloc_ctor(1, 1, 0); \
    lean_ctor_set(some, 0, fields)

#define UNMARSHAL_TM(a) \
    struct tm tm = {0}; \
    tm.tm_sec = (int32_t)lean_unbox_uint32(lean_array_get_core(a, 0)); \
    tm.tm_min = (int32_t)lean_unbox_uint32(lean_array_get_core(a, 1)); \
    tm.tm_hour = (int32_t)lean_unbox_uint32(lean_array_get_core(a, 2)); \
    tm.tm_mday = (int32_t)lean_unbox_uint32(lean_array_get_core(a, 3)); \
    tm.tm_mon = (int32_t)lean_unbox_uint32(lean_array_get_core(a, 4)); \
    tm.tm_year = (int32_t)lean_unbox_uint32(lean_array_get_core(a, 5)); \
    tm.tm_wday = (int32_t)lean_unbox_uint32(lean_array_get_core(a, 6)); \
    tm.tm_yday = (int32_t)lean_unbox_uint32(lean_array_get_core(a, 7)); \
    tm.tm_isdst = (int32_t)lean_unbox_uint32(lean_array_get_core(a, 8))

LEAN_EXPORT lean_obj_res lean_corelogs_gmtime(uint64_t seconds) {
    time_t value = (time_t)seconds;
    struct tm tm;
    if (!gmtime_r(&value, &tm)) return ls_ok(lean_box(0));
    MARSHAL_TM(tm);
    return ls_ok(some);
}

LEAN_EXPORT lean_obj_res lean_corelogs_localtime(uint64_t seconds) {
    time_t value = (time_t)seconds;
    struct tm tm;
    if (!localtime_r(&value, &tm)) return ls_ok(lean_box(0));
    MARSHAL_TM(tm);
    return ls_ok(some);
}

LEAN_EXPORT lean_obj_res lean_corelogs_mktime(b_lean_obj_arg fields) {
    if (lean_array_size(fields) < 9)
        return lean_io_result_mk_error(lean_decode_io_error(EINVAL, NULL));
    UNMARSHAL_TM(fields);
    time_t value = mktime(&tm);
    return ls_ok(lean_box_uint64((uint64_t)value));
}

LEAN_EXPORT lean_obj_res lean_corelogs_langinfo(uint32_t item, uint32_t capacity) {
    const char *value = nl_langinfo(item);
    size_t size = strnlen(value, capacity);
    lean_object *bytes = lean_alloc_sarray(1, size, size);
    if (size) memcpy(lean_sarray_cptr(bytes), value, size);
    return ls_ok(bytes);
}

LEAN_EXPORT lean_obj_res lean_corelogs_lower_byte(uint32_t byte) {
    return ls_ok(lean_box_uint32(tolower((unsigned char)byte)));
}

LEAN_EXPORT lean_obj_res lean_corelogs_upper_byte(uint32_t byte) {
    return ls_ok(lean_box_uint32(toupper((unsigned char)byte)));
}

LEAN_EXPORT lean_obj_res lean_corelogs_uname(void) {
    struct utsname u;
    int rc = uname(&u);
    int error = rc < 0 ? errno : 0;
    return ls_ok(ls_pair(lean_box_uint32(error), lean_mk_string(rc < 0 ? "" : u.machine)));
}

LEAN_EXPORT lean_obj_res lean_corelogs_prctl(void) {
    int rc = prctl(PR_GET_NO_NEW_PRIVS, 0, 0, 0, 0);
    return ls_ok(lean_int_to_int(rc));
}

LEAN_EXPORT lean_obj_res lean_corelogs_open(b_lean_obj_arg path, uint32_t flags, uint32_t mode) {
    int rc = open(lean_string_cstr(path), flags, mode);
    return ls_ok(lean_int_to_int(rc < 0 ? -errno : rc));
}

LEAN_EXPORT lean_obj_res lean_corelogs_close(uint32_t fd) {
    int rc = close(fd);
    return ls_ok(lean_int_to_int(rc < 0 ? -errno : rc));
}

LEAN_EXPORT lean_obj_res lean_corelogs_fstat(uint32_t fd) {
    struct stat st;
    if (fstat(fd, &st) != 0) return ls_ok(lean_box(0));
    lean_object *a = lean_mk_empty_array_with_capacity(lean_box(3));
    a = lean_array_push(a, lean_uint64_to_nat(st.st_mode));
    a = lean_array_push(a, lean_uint64_to_nat(st.st_uid));
    a = lean_array_push(a, lean_uint64_to_nat((uint64_t)st.st_size));
    lean_object *some = lean_alloc_ctor(1, 1, 0);
    lean_ctor_set(some, 0, a);
    return ls_ok(some);
}

LEAN_EXPORT lean_obj_res lean_corelogs_winsize(uint32_t fd) {
    struct winsize ws = {0};
    int rc = ioctl(fd, TIOCGWINSZ, &ws);
    int error = rc < 0 ? errno : 0;
    return ls_ok(ls_pair(lean_box_uint32(error),
        ls_pair(lean_box(ws.ws_col), lean_box(ws.ws_row))));
}

LEAN_EXPORT lean_obj_res lean_corelogs_flock(uint32_t fd, uint32_t operation) {
    int rc = flock(fd, operation);
    return ls_ok(lean_int_to_int(rc < 0 ? -errno : rc));
}

LEAN_EXPORT lean_obj_res lean_corelogs_seek(uint32_t fd, uint64_t offset, uint32_t whence) {
    off_t rc = lseek(fd, (int64_t)offset, whence);
    return ls_ok(lean_int64_to_int(rc < 0 ? -errno : rc));
}

LEAN_EXPORT lean_obj_res lean_corelogs_write(uint32_t fd, b_lean_obj_arg bytes, size_t offset) {
    if (offset > lean_sarray_size(bytes)) return ls_ok(lean_int_to_int(-EINVAL));
    ssize_t rc = write(fd, lean_sarray_cptr(bytes) + offset, lean_sarray_size(bytes) - offset);
    return ls_ok(lean_int64_to_int(rc < 0 ? -errno : rc));
}

LEAN_EXPORT lean_obj_res lean_corelogs_random(uint32_t size) {
    lean_object *bytes = lean_alloc_sarray(1, size, size);
    ssize_t rc = getrandom(lean_sarray_cptr(bytes), size, 0);
    int error = rc < 0 ? errno : 0;
    lean_sarray_set_size(bytes, rc < 0 ? 0 : (size_t)rc);
    return ls_ok(ls_pair(lean_box_uint32(error), bytes));
}

LEAN_EXPORT lean_obj_res lean_corelogs_rtmin(void) {
    return ls_ok(lean_box_uint32(SIGRTMIN));
}

LEAN_EXPORT lean_obj_res lean_corelogs_rtmax(void) {
    return ls_ok(lean_box_uint32(SIGRTMAX));
}
