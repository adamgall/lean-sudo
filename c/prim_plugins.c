#define __STDC_WANT_LIB_EXT1__ 1
#include "shim.h"
#include "sudo_plugin.h"
#include <dlfcn.h>
#include <errno.h>
#include <fcntl.h>
#include <limits.h>
#include <poll.h>
#include <signal.h>
#include <stddef.h>
#include <stdarg.h>
#include <stdatomic.h>
#include <stdio.h>
#include <sys/ioctl.h>
#include <sys/resource.h>
#include <time.h>
#include <unistd.h>
#ifdef __linux__
#include <linux/major.h>
#include <sys/sysmacros.h>
#endif

LEAN_EXPORT uintptr_t lean_sudo_pp_constant(uint32_t index) {
    static const uintptr_t values[] = {
        sizeof(void *), sizeof(struct sudo_conv_message),
        offsetof(struct sudo_conv_message, msg_type),
        offsetof(struct sudo_conv_message, timeout), offsetof(struct sudo_conv_message, msg),
        sizeof(struct sudo_conv_reply), offsetof(struct sudo_conv_reply, reply),
        offsetof(struct sudo_hook, hook_version), offsetof(struct sudo_hook, hook_type),
        offsetof(struct sudo_hook, hook_fn), offsetof(struct sudo_hook, closure),
        offsetof(struct sudo_conv_callback, version),
        offsetof(struct io_plugin, type), offsetof(struct io_plugin, version),
        offsetof(struct io_plugin, open), offsetof(struct io_plugin, close),
        offsetof(struct io_plugin, show_version), offsetof(struct io_plugin, log_ttyin),
        offsetof(struct io_plugin, log_ttyout), offsetof(struct io_plugin, log_stdin),
        offsetof(struct io_plugin, log_stdout), offsetof(struct io_plugin, log_stderr),
        offsetof(struct io_plugin, register_hooks), offsetof(struct io_plugin, deregister_hooks),
        offsetof(struct io_plugin, change_winsize), offsetof(struct io_plugin, log_suspend),
        offsetof(struct io_plugin, event_alloc),
        offsetof(struct audit_plugin, open), offsetof(struct audit_plugin, close),
        offsetof(struct audit_plugin, accept), offsetof(struct audit_plugin, reject),
        offsetof(struct audit_plugin, error), offsetof(struct audit_plugin, show_version),
        offsetof(struct audit_plugin, register_hooks),
        offsetof(struct audit_plugin, deregister_hooks),
        offsetof(struct audit_plugin, event_alloc),
        offsetof(struct approval_plugin, open), offsetof(struct approval_plugin, close),
        offsetof(struct approval_plugin, check), offsetof(struct approval_plugin, show_version),
        ENOTSUP, POLLIN, POLLOUT, POLLHUP | POLLERR | POLLNVAL, NSIG,
        RLIMIT_AS, RLIMIT_CORE, RLIMIT_CPU, RLIMIT_DATA, RLIMIT_FSIZE,
#ifdef RLIMIT_LOCKS
        RLIMIT_LOCKS,
#else
        UINT32_MAX,
#endif
        RLIMIT_MEMLOCK, RLIMIT_NOFILE, RLIMIT_NPROC, RLIMIT_RSS, RLIMIT_STACK, RLIM_INFINITY,
#ifdef __linux__
        UNIX98_PTY_SLAVE_MAJOR, UNIX98_PTY_MAJOR_COUNT, TTY_MAJOR, 1,
#else
        0, 0, 0, 0,
#endif
        256, 64, NGROUPS_MAX
    };
    return values[index];
}

#define PP_CONSTANT(name, type, index) \
    LEAN_EXPORT type lean_sudo_pp_##name(b_lean_obj_arg unit) { \
        (void)unit; \
        return (type)lean_sudo_pp_constant(index); \
    }
PP_CONSTANT(pointerSize, uintptr_t, 0)
PP_CONSTANT(messageSize, uintptr_t, 1)
PP_CONSTANT(messageType, uintptr_t, 2)
PP_CONSTANT(messageTimeout, uintptr_t, 3)
PP_CONSTANT(messageText, uintptr_t, 4)
PP_CONSTANT(replySize, uintptr_t, 5)
PP_CONSTANT(replyValue, uintptr_t, 6)
PP_CONSTANT(hookVersion, uintptr_t, 7)
PP_CONSTANT(hookType, uintptr_t, 8)
PP_CONSTANT(hookFunction, uintptr_t, 9)
PP_CONSTANT(hookClosure, uintptr_t, 10)
PP_CONSTANT(conversationVersion, uintptr_t, 11)
PP_CONSTANT(pluginType, uintptr_t, 12)
PP_CONSTANT(pluginVersion, uintptr_t, 13)
PP_CONSTANT(unsupported, uint32_t, 40)
PP_CONSTANT(pollIn, uint32_t, 41)
PP_CONSTANT(pollOut, uint32_t, 42)
PP_CONSTANT(pollFailed, uint32_t, 43)
PP_CONSTANT(signalCount, uint32_t, 44)
PP_CONSTANT(limitInfinity, uint64_t, 56)
PP_CONSTANT(ptySlaveMajor, uint32_t, 57)
PP_CONSTANT(ptyMajorCount, uint32_t, 58)
PP_CONSTANT(ttyMajor, uint32_t, 59)
PP_CONSTANT(linuxDevices, uint8_t, 60)
PP_CONSTANT(ptyMinorCount, uint32_t, 61)
PP_CONSTANT(ttySerialBase, uint32_t, 62)
PP_CONSTANT(groupsFallback, uint32_t, 63)
#undef PP_CONSTANT

LEAN_EXPORT lean_obj_res lean_sudo_pp_timespec_get(uintptr_t ptr) {
    const struct timespec *t = (void *)ptr;
    return ls_ok(ls_pair(lean_box_uint64(t->tv_sec), lean_box_uint64(t->tv_nsec)));
}
LEAN_EXPORT lean_obj_res lean_sudo_pp_timespec_set(uintptr_t ptr, uint64_t sec, uint64_t nsec) {
    *(struct timespec *)ptr = (struct timespec){(time_t)sec, (long)nsec};
    return ls_unit();
}
LEAN_EXPORT uint32_t lean_sudo_pp_dev_major(uint64_t dev) {
    return major((dev_t)dev);
}
LEAN_EXPORT uint32_t lean_sudo_pp_dev_minor(uint64_t dev) {
    return minor((dev_t)dev);
}

static _Atomic(lean_object *) dispatcher;
static atomic_flag dispatcher_claimed = ATOMIC_FLAG_INIT;
static _Thread_local pid_t dispatcher_pid;
typedef char *(*getenv_fn)(const char *);
typedef int (*setenv_fn)(const char *, const char *, int);
typedef int (*unsetenv_fn)(const char *);
typedef int (*putenv_fn)(char *);
static _Atomic(getenv_fn) libc_getenv_slot;
static _Atomic(setenv_fn) libc_setenv_slot;
static _Atomic(unsetenv_fn) libc_unsetenv_slot;
static _Atomic(putenv_fn) libc_putenv_slot;
static getenv_fn libc_getenv(void) {
    getenv_fn f = atomic_load_explicit(&libc_getenv_slot, memory_order_acquire);
    if (f) return f;
    f = (getenv_fn)dlsym(RTLD_NEXT, "getenv");
    atomic_store_explicit(&libc_getenv_slot, f, memory_order_release);
    return f;
}
static setenv_fn libc_setenv(void) {
    setenv_fn f = atomic_load_explicit(&libc_setenv_slot, memory_order_acquire);
    if (f) return f;
    f = (setenv_fn)dlsym(RTLD_NEXT, "setenv");
    atomic_store_explicit(&libc_setenv_slot, f, memory_order_release);
    return f;
}
static unsetenv_fn libc_unsetenv(void) {
    unsetenv_fn f = atomic_load_explicit(&libc_unsetenv_slot, memory_order_acquire);
    if (f) return f;
    f = (unsetenv_fn)dlsym(RTLD_NEXT, "unsetenv");
    atomic_store_explicit(&libc_unsetenv_slot, f, memory_order_release);
    return f;
}
static putenv_fn libc_putenv(void) {
    putenv_fn f = atomic_load_explicit(&libc_putenv_slot, memory_order_acquire);
    if (f) return f;
    f = (putenv_fn)dlsym(RTLD_NEXT, "putenv");
    atomic_store_explicit(&libc_putenv_slot, f, memory_order_release);
    return f;
}
static lean_object *thread_dispatcher(void) {
    if (!dispatcher_pid || dispatcher_pid != getpid()) return NULL;
    return atomic_load_explicit(&dispatcher, memory_order_acquire);
}
static uintptr_t dispatch_callback(lean_object *callback, unsigned op, uintptr_t a,
    uintptr_t b, uintptr_t c, uintptr_t d, uintptr_t e) {
    lean_inc(callback);
    lean_object *r = lean_apply_7(callback, lean_box_uint32(op), lean_box_usize(a),
        lean_box_usize(b), lean_box_usize(c), lean_box_usize(d), lean_box_usize(e), lean_box(0));
    uintptr_t value = UINTPTR_MAX;
    if (lean_io_result_is_ok(r)) value = lean_unbox_usize(lean_io_result_get_value(r));
    lean_dec(r);
    return value;
}
static uintptr_t dispatch(unsigned op, uintptr_t a, uintptr_t b,
    uintptr_t c, uintptr_t d, uintptr_t e) {
    lean_object *callback = thread_dispatcher();
    if (!callback) { errno = ENOSYS; return UINTPTR_MAX; }
    return dispatch_callback(callback, op, a, b, c, d, e);
}
LEAN_EXPORT lean_obj_res lean_sudo_pp_install(lean_obj_arg callback) {
    pid_t pid = getpid();
    if (!atomic_flag_test_and_set_explicit(&dispatcher_claimed, memory_order_acq_rel))
        dispatcher_pid = pid;
    if (!dispatcher_pid || dispatcher_pid != pid) {
        lean_dec(callback);
        return lean_io_result_mk_error(lean_mk_io_user_error(
            lean_mk_string("plugin dispatcher requires the original main thread")));
    }
    lean_mark_mt(callback);
    lean_object *previous = atomic_exchange_explicit(&dispatcher, callback, memory_order_acq_rel);
    if (previous) lean_dec(previous);
    return ls_unit();
}
char *getenv(const char *name) {
    lean_object *callback = thread_dispatcher();
    if (callback) {
        uintptr_t result = dispatch_callback(callback, 10, (uintptr_t)name, 0, 0, 0, 0);
        return result == UINTPTR_MAX ? NULL : (char *)result;
    }
    getenv_fn real = libc_getenv();
    if (!real) { errno = ENOSYS; return NULL; }
    return real(name);
}
int setenv(const char *name, const char *value, int overwrite) {
    lean_object *callback = thread_dispatcher();
    if (callback)
        return (int)dispatch_callback(callback, 11,
            (uintptr_t)name, (uintptr_t)value, overwrite, 0, 0);
    setenv_fn real = libc_setenv();
    if (!real) { errno = ENOSYS; return -1; }
    return real(name, value, overwrite);
}
int unsetenv(const char *name) {
    lean_object *callback = thread_dispatcher();
    if (callback) return (int)dispatch_callback(callback, 12, (uintptr_t)name, 0, 0, 0, 0);
    unsetenv_fn real = libc_unsetenv();
    if (!real) { errno = ENOSYS; return -1; }
    return real(name);
}
int putenv(char *value) {
    lean_object *callback = thread_dispatcher();
    if (callback) return (int)dispatch_callback(callback, 13, (uintptr_t)value, 0, 0, 0, 0);
    putenv_fn real = libc_putenv();
    if (!real) { errno = ENOSYS; return -1; }
    return real(value);
}
static int conversation(int n, const struct sudo_conv_message *m,
    struct sudo_conv_reply *r, struct sudo_conv_callback *cb) {
    return (int)dispatch(0, n, (uintptr_t)m, (uintptr_t)r, (uintptr_t)cb, 0);
}
static int conversation_old(int n, const struct sudo_conv_message *m,
    struct sudo_conv_reply *r) {
    return (int)dispatch(0, n, (uintptr_t)m, (uintptr_t)r, 0, 0);
}
static int plugin_printf(int type, const char *restrict fmt, ...) {
    lean_object *callback = thread_dispatcher();
    if (!callback) { errno = ENOSYS; return -1; }
    char stack[4096], *text = stack;
    va_list args, copy;
    va_start(args, fmt);
    va_copy(copy, args);
    int size = vsnprintf(stack, sizeof stack, fmt, args);
    va_end(args);
    if (size < 0) { va_end(copy); return -1; }
    if ((size_t)size >= sizeof stack) {
        text = malloc((size_t)size + 1);
        if (!text) { va_end(copy); return -1; }
        vsnprintf(text, (size_t)size + 1, fmt, copy);
    }
    va_end(copy);
    int result = (int)dispatch_callback(callback, 1, type, (uintptr_t)text, (uintptr_t)size, 0, 0);
    if (text != stack) free(text);
    return result;
}
static int register_hook(struct sudo_hook *h) {
    return (int)dispatch(2, (uintptr_t)h, 0, 0, 0, 0);
}
static int deregister_hook(struct sudo_hook *h) {
    return (int)dispatch(3, (uintptr_t)h, 0, 0, 0, 0);
}
static int event_set(struct sudo_plugin_event *ev, int fd, int flags,
    sudo_plugin_ev_callback_t cb, void *closure) {
    return (int)dispatch(20, (uintptr_t)ev, fd, flags, (uintptr_t)cb, (uintptr_t)closure);
}
static int event_add(struct sudo_plugin_event *ev, struct timespec *timeout) {
    return (int)dispatch(21, (uintptr_t)ev, (uintptr_t)timeout, 0, 0, 0);
}
static int event_del(struct sudo_plugin_event *ev) {
    return (int)dispatch(22, (uintptr_t)ev, 0, 0, 0, 0);
}
static int event_pending(struct sudo_plugin_event *ev, int flags, struct timespec *timeout) {
    return (int)dispatch(23, (uintptr_t)ev, flags, (uintptr_t)timeout, 0, 0);
}
static int event_fd(struct sudo_plugin_event *ev) {
    return (int)dispatch(24, (uintptr_t)ev, 0, 0, 0, 0);
}
static void event_setbase(struct sudo_plugin_event *ev, void *base) {
    (void)dispatch(25, (uintptr_t)ev, (uintptr_t)base, 0, 0, 0);
}
static void event_loopbreak(struct sudo_plugin_event *ev) {
    (void)dispatch(26, (uintptr_t)ev, 0, 0, 0, 0);
}
static void event_free(struct sudo_plugin_event *ev) {
    (void)dispatch(27, (uintptr_t)ev, 0, 0, 0, 0);
}
static struct sudo_plugin_event *event_alloc(void) {
    uintptr_t result = dispatch(28, 0, 0, 0, 0, 0);
    return result == UINTPTR_MAX ? NULL : (void *)result;
}
LEAN_EXPORT lean_obj_res lean_sudo_pp_event_alloc(void) {
    struct sudo_plugin_event *e = malloc(sizeof(*e));
    if (e) *e = (struct sudo_plugin_event){event_set, event_add, event_del, event_pending,
        event_fd, event_setbase, event_loopbreak, event_free};
    return ls_ok(lean_box_usize((uintptr_t)e));
}
LEAN_EXPORT lean_obj_res lean_sudo_pp_event_setter(uintptr_t slot) {
    *(struct sudo_plugin_event *(**)(void))slot = event_alloc;
    return ls_unit();
}
LEAN_EXPORT lean_obj_res lean_sudo_pp_dlopen(b_lean_obj_arg path) {
    void *handle = dlopen(lean_string_cstr(path), RTLD_LAZY | RTLD_GLOBAL);
    return ls_ok(lean_box_usize((uintptr_t)handle));
}
LEAN_EXPORT lean_obj_res lean_sudo_pp_dlsym(uintptr_t handle, b_lean_obj_arg name) {
    return ls_ok(lean_box_usize((uintptr_t)dlsym((void *)handle, lean_string_cstr(name))));
}
LEAN_EXPORT lean_obj_res lean_sudo_pp_dlerror(void) {
    const char *s = dlerror();
    if (!s) return ls_ok(lean_box(0));
    lean_object *value = lean_alloc_ctor(1, 1, 0);
    lean_ctor_set(value, 0, lean_mk_string(s));
    return ls_ok(value);
}
LEAN_EXPORT lean_obj_res lean_sudo_pp_dlclose(uintptr_t handle) {
    return ls_ok(lean_box_uint32(dlclose((void *)handle)));
}
LEAN_EXPORT lean_obj_res lean_sudo_pp_alloc(uintptr_t size) {
    return ls_ok(lean_box_usize((uintptr_t)calloc(1, size)));
}
LEAN_EXPORT lean_obj_res lean_sudo_pp_free(uintptr_t ptr) {
    free((void *)ptr);
    return ls_unit();
}
LEAN_EXPORT lean_obj_res lean_sudo_pp_erase(uintptr_t ptr, uintptr_t size) {
#ifdef __APPLE__
    memset_s((void *)ptr, size, 0, size);
#else
    explicit_bzero((void *)ptr, size);
#endif
    return ls_unit();
}
LEAN_EXPORT lean_obj_res lean_sudo_pp_dup(b_lean_obj_arg text) {
    return ls_ok(lean_box_usize((uintptr_t)strdup(lean_string_cstr(text))));
}
LEAN_EXPORT lean_obj_res lean_sudo_pp_dup_bytes(b_lean_obj_arg data) {
    char *copy = strndup((const char *)lean_sarray_cptr(data), lean_sarray_size(data));
    return ls_ok(lean_box_usize((uintptr_t)copy));
}
LEAN_EXPORT lean_obj_res lean_sudo_pp_string(uintptr_t ptr) {
    return ls_ok(lean_mk_string((const char *)ptr));
}
LEAN_EXPORT lean_obj_res lean_sudo_pp_length(uintptr_t ptr) {
    return ls_ok(lean_box_usize(strlen((const char *)ptr)));
}
LEAN_EXPORT lean_obj_res lean_sudo_pp_read_ptr(uintptr_t ptr, uintptr_t offset) {
    return ls_ok(lean_box_usize(*(uintptr_t *)(ptr + offset)));
}
LEAN_EXPORT lean_obj_res lean_sudo_pp_write_ptr(uintptr_t ptr, uintptr_t offset, uintptr_t value) {
    *(uintptr_t *)(ptr + offset) = value;
    return ls_unit();
}
LEAN_EXPORT lean_obj_res lean_sudo_pp_read_u32(uintptr_t ptr, uintptr_t offset) {
    return ls_ok(lean_box_uint32(*(uint32_t *)(ptr + offset)));
}
LEAN_EXPORT lean_obj_res lean_sudo_pp_errno(uint32_t value) {
    errno = value;
    return ls_unit();
}
LEAN_EXPORT lean_obj_res lean_sudo_pp_write(uint32_t fd, uintptr_t ptr, uintptr_t size) {
    return ls_ok(lean_box_usize(write((int)fd, (void *)ptr, size)));
}
LEAN_EXPORT lean_obj_res lean_sudo_pp_open_tty(uint32_t flags) {
    return ls_ok(lean_box_uint32(open("/dev/tty", (int)flags)));
}
LEAN_EXPORT lean_obj_res lean_sudo_pp_close_fd(uint32_t fd) {
    return ls_ok(lean_box_uint32(close((int)fd)));
}
LEAN_EXPORT lean_obj_res lean_sudo_pp_now(void) {
    struct timespec t = {0};
    int rc = clock_gettime(CLOCK_MONOTONIC, &t);
    int error = rc < 0 ? errno : 0;
    return ls_ok(ls_pair(lean_box_uint32(error),
        ls_pair(lean_box_uint64(t.tv_sec), lean_box_uint64(t.tv_nsec))));
}
LEAN_EXPORT lean_obj_res lean_sudo_pp_poll(uint32_t fd, uint32_t events) {
    struct pollfd p = {(int)fd, (short)events, 0};
    int rc = poll(&p, 1, 0);
    int error = rc < 0 ? errno : 0;
    return ls_ok(ls_pair(lean_box_uint32(error), lean_box_uint32((unsigned short)p.revents)));
}
LEAN_EXPORT lean_obj_res lean_sudo_pp_strerror(uint32_t error) {
    return ls_ok(lean_mk_string(strerror((int)error)));
}
LEAN_EXPORT lean_obj_res lean_sudo_pp_getpid(void) {
    return ls_ok(lean_box_uint32(getpid()));
}
LEAN_EXPORT lean_obj_res lean_sudo_pp_getppid(void) {
    return ls_ok(lean_box_uint32(getppid()));
}
LEAN_EXPORT lean_obj_res lean_sudo_pp_getpgrp(void) {
    return ls_ok(lean_box_uint32(getpgrp()));
}
LEAN_EXPORT lean_obj_res lean_sudo_pp_getsid(void) {
    return ls_ok(lean_box_uint32(getsid(0)));
}
LEAN_EXPORT lean_obj_res lean_sudo_pp_tcgetpgrp(uint32_t fd) {
    return ls_ok(lean_box_uint32(tcgetpgrp(fd)));
}
LEAN_EXPORT lean_obj_res lean_sudo_pp_winsize(uint32_t fd) {
    struct winsize ws = {0};
    int rc = ioctl(fd, TIOCGWINSZ, &ws);
    if (rc < 0) return ls_ok(lean_box(0));
    lean_object *value = lean_alloc_ctor(1, 1, 0);
    lean_ctor_set(value, 0, ls_pair(lean_box_uint32(ws.ws_row), lean_box_uint32(ws.ws_col)));
    return ls_ok(value);
}
LEAN_EXPORT lean_obj_res lean_sudo_pp_ttydev(uint32_t fd) {
    unsigned dev = 0;
#ifdef TIOCGDEV
    if (ioctl(fd, TIOCGDEV, &dev) < 0) return ls_ok(lean_box(0));
#else
    (void)fd;
    return ls_ok(lean_box(0));
#endif
    lean_object *v = lean_alloc_ctor(1, 1, 0);
    lean_ctor_set(v, 0, lean_box_uint32(dev));
    return ls_ok(v);
}
LEAN_EXPORT lean_obj_res lean_sudo_pp_group_max(void) {
    return ls_ok(lean_box_usize(sysconf(_SC_NGROUPS_MAX)));
}
LEAN_EXPORT lean_obj_res lean_sudo_pp_rlimit(uint32_t resource) {
    struct rlimit r;
    if (getrlimit(resource, &r)) return ls_ok(lean_box(0));
    lean_object *v = lean_alloc_ctor(1, 1, 0);
    lean_ctor_set(v, 0, ls_pair(lean_box_uint64(r.rlim_cur), lean_box_uint64(r.rlim_max)));
    return ls_ok(v);
}
static lean_object *call_result(int rc, const char *why) {
    lean_object *option = lean_box(0);
    if (why) {
        option = lean_alloc_ctor(1, 1, 0);
        lean_ctor_set(option, 0, lean_mk_string(why));
    }
    return ls_ok(ls_pair(lean_box_uint32(rc), option));
}
LEAN_EXPORT lean_obj_res lean_sudo_pp_clone(uintptr_t fn) {
    return ls_ok(lean_box_usize((uintptr_t)((void *(*)(void))fn)()));
}
LEAN_EXPORT lean_obj_res lean_sudo_pp_hooks(uintptr_t fn, uint8_t add) {
    ((void (*)(int, int (*)(struct sudo_hook *)))fn)(SUDO_HOOK_VERSION,
        add ? register_hook : deregister_hook);
    return ls_unit();
}
LEAN_EXPORT lean_obj_res lean_sudo_pp_open_common(uintptr_t fn, uintptr_t s, uintptr_t u,
    uint32_t index, uintptr_t a, uintptr_t e, uintptr_t o) {
    const char *why = NULL;
    int rc = ((int (*)(unsigned, sudo_conv_t, sudo_printf_t, char **, char **, int,
        char **, char **, char **, const char **))fn)(SUDO_API_VERSION, conversation,
        plugin_printf, (char **)s, (char **)u, index, (char **)a, (char **)e, (char **)o, &why);
    return call_result(rc, why);
}
LEAN_EXPORT lean_obj_res lean_sudo_pp_open_io0(uintptr_t fn, uintptr_t s, uintptr_t u,
    uint32_t count, uintptr_t a, uintptr_t e) {
    int rc = ((int (*)(unsigned, void *, sudo_printf_t, char **, char **, int,
        char **, char **))fn)(SUDO_API_MKVERSION(1, 0), conversation_old, plugin_printf,
        (char **)s, (char **)u, count, (char **)a, (char **)e);
    return call_result(rc, NULL);
}
LEAN_EXPORT lean_obj_res lean_sudo_pp_open_io1(uintptr_t fn, uintptr_t s, uintptr_t u,
    uintptr_t info, uint32_t count, uintptr_t a, uintptr_t e) {
    int rc = ((int (*)(unsigned, void *, sudo_printf_t, char **, char **, char **, int,
        char **, char **))fn)(SUDO_API_MKVERSION(1, 1), conversation_old, plugin_printf,
        (char **)s, (char **)u, (char **)info, count, (char **)a, (char **)e);
    return call_result(rc, NULL);
}
LEAN_EXPORT lean_obj_res lean_sudo_pp_open_io2(uintptr_t fn, uintptr_t s, uintptr_t u,
    uintptr_t info, uint32_t count, uintptr_t a, uintptr_t e, uintptr_t o) {
    int rc = ((int (*)(unsigned, sudo_conv_t, sudo_printf_t, char **, char **, char **,
        int, char **, char **, char **))fn)(SUDO_API_VERSION, conversation, plugin_printf,
        (char **)s, (char **)u, (char **)info, count, (char **)a, (char **)e, (char **)o);
    return call_result(rc, NULL);
}
LEAN_EXPORT lean_obj_res lean_sudo_pp_open_io(uintptr_t fn, uintptr_t s, uintptr_t u,
    uintptr_t info, uint32_t count, uintptr_t a, uintptr_t e, uintptr_t o) {
    const char *why = NULL;
    int rc = ((int (*)(unsigned, sudo_conv_t, sudo_printf_t, char **, char **, char **,
        int, char **, char **, char **, const char **))fn)(SUDO_API_VERSION, conversation,
        plugin_printf, (char **)s, (char **)u, (char **)info, count,
        (char **)a, (char **)e, (char **)o, &why);
    return call_result(rc, why);
}
LEAN_EXPORT lean_obj_res lean_sudo_pp_accept(uintptr_t fn, b_lean_obj_arg name,
    uint32_t type, uintptr_t info, uintptr_t a, uintptr_t e) {
    const char *why = NULL;
    int rc = ((int (*)(const char *, unsigned, char **, char **, char **, const char **))fn)(
        lean_string_cstr(name), type, (char **)info, (char **)a, (char **)e, &why);
    return call_result(rc, why);
}
LEAN_EXPORT lean_obj_res lean_sudo_pp_message(uintptr_t fn, b_lean_obj_arg name,
    uint32_t type, b_lean_obj_arg message, uintptr_t info) {
    const char *why = NULL;
    int rc = ((int (*)(const char *, unsigned, const char *, char **, const char **))fn)(
        lean_string_cstr(name), type, lean_string_cstr(message), (char **)info, &why);
    return call_result(rc, why);
}
LEAN_EXPORT lean_obj_res lean_sudo_pp_check(uintptr_t fn, uintptr_t info,
    uintptr_t a, uintptr_t e) {
    const char *why = NULL;
    int rc = ((int (*)(char **, char **, char **, const char **))fn)(
        (char **)info, (char **)a, (char **)e, &why);
    return call_result(rc, why);
}
LEAN_EXPORT lean_obj_res lean_sudo_pp_close(uintptr_t fn, uint32_t a, uint32_t b) {
    ((void (*)(int, int))fn)(a, b);
    return ls_unit();
}
LEAN_EXPORT lean_obj_res lean_sudo_pp_close0(uintptr_t fn) {
    ((void (*)(void))fn)();
    return ls_unit();
}
LEAN_EXPORT lean_obj_res lean_sudo_pp_int(uintptr_t fn, uint32_t arg) {
    return ls_ok(lean_box_uint32(((int (*)(int))fn)(arg)));
}
LEAN_EXPORT lean_obj_res lean_sudo_pp_log(uintptr_t fn, b_lean_obj_arg data) {
    const char *why = NULL;
    int rc = ((int (*)(const char *, unsigned, const char **))fn)(
        (const char *)lean_sarray_cptr(data), lean_sarray_size(data), &why);
    return call_result(rc, why);
}
LEAN_EXPORT lean_obj_res lean_sudo_pp_log_old(uintptr_t fn, b_lean_obj_arg data) {
    int rc = ((int (*)(const char *, unsigned))fn)(
        (const char *)lean_sarray_cptr(data), lean_sarray_size(data));
    return call_result(rc, NULL);
}
LEAN_EXPORT lean_obj_res lean_sudo_pp_suspend(uintptr_t fn, uint32_t signo) {
    const char *why = NULL;
    int rc = ((int (*)(int, const char **))fn)(signo, &why);
    return call_result(rc, why);
}
LEAN_EXPORT lean_obj_res lean_sudo_pp_window(uintptr_t fn, uint32_t rows, uint32_t cols) {
    const char *why = NULL;
    int rc = ((int (*)(unsigned, unsigned, const char **))fn)(rows, cols, &why);
    return call_result(rc, why);
}
LEAN_EXPORT lean_obj_res lean_sudo_pp_window_old(uintptr_t fn, uint32_t rows, uint32_t cols) {
    return ls_ok(lean_box_uint32(((int (*)(unsigned, unsigned))fn)(rows, cols)));
}
LEAN_EXPORT lean_obj_res lean_sudo_pp_event(uintptr_t fn, uint32_t fd,
    uint32_t what, uintptr_t closure) {
    ((sudo_plugin_ev_callback_t)fn)(fd, what, (void *)closure);
    return ls_unit();
}
LEAN_EXPORT lean_obj_res lean_sudo_pp_hook_get(uintptr_t fn, uintptr_t name, uintptr_t closure) {
    char *value = NULL;
    int rc = ((sudo_hook_fn_getenv_t)fn)((const char *)name, &value, (void *)closure);
    return ls_ok(ls_pair(lean_box_uint32(rc), lean_box_usize((uintptr_t)value)));
}
LEAN_EXPORT lean_obj_res lean_sudo_pp_hook_set(uintptr_t fn, uintptr_t name,
    uintptr_t value, uint32_t overwrite, uintptr_t closure) {
    return ls_ok(lean_box_uint32(((sudo_hook_fn_setenv_t)fn)(
        (const char *)name, (const char *)value, overwrite, (void *)closure)));
}
LEAN_EXPORT lean_obj_res lean_sudo_pp_hook_unset(uintptr_t fn, uintptr_t name,
    uintptr_t closure) {
    return ls_ok(lean_box_uint32(((sudo_hook_fn_unsetenv_t)fn)(
        (const char *)name, (void *)closure)));
}
LEAN_EXPORT lean_obj_res lean_sudo_pp_real_get(uintptr_t name) {
    getenv_fn real = libc_getenv();
    if (!real) { errno = ENOSYS; return ls_ok(lean_box_usize(0)); }
    return ls_ok(lean_box_usize((uintptr_t)real((const char *)name)));
}
LEAN_EXPORT lean_obj_res lean_sudo_pp_real_set(uintptr_t name, uintptr_t value,
    uint32_t overwrite) {
    setenv_fn real = libc_setenv();
    if (!real) { errno = ENOSYS; return ls_ok(lean_box_uint32(-1)); }
    return ls_ok(lean_box_uint32(real((const char *)name, (const char *)value, overwrite)));
}
LEAN_EXPORT lean_obj_res lean_sudo_pp_real_unset(uintptr_t name) {
    unsetenv_fn real = libc_unsetenv();
    if (!real) { errno = ENOSYS; return ls_ok(lean_box_uint32(-1)); }
    return ls_ok(lean_box_uint32(real((const char *)name)));
}
LEAN_EXPORT lean_obj_res lean_sudo_pp_real_put(uintptr_t value) {
    putenv_fn real = libc_putenv();
    if (!real) { errno = ENOSYS; return ls_ok(lean_box_uint32(-1)); }
    return ls_ok(lean_box_uint32(real((char *)value)));
}
