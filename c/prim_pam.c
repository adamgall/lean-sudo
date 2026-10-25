#include "shim.h"
#include "sudo_plugin.h"
#include <errno.h>
#include <fcntl.h>
#include <stddef.h>
#include <libintl.h>
#include <poll.h>
#include <signal.h>
#include <string.h>
#include <sys/signalfd.h>
#include <termios.h>
#include <unistd.h>

enum {
    PAM_SUCCESS = 0, PAM_BUF_ERR = 5, PAM_AUTH_ERR = 7, PAM_CONV_ERR = 19,
    PAM_SILENT = 0x8000, PAM_CHANGE_EXPIRED_AUTHTOK = 0x20,
    PAM_REINITIALIZE_CRED = 8, PAM_DELETE_CRED = 4,
    PAM_TTY = 3, PAM_RUSER = 8, PAM_RHOST = 4, PAM_USER = 2,
    PAM_PROMPT_ECHO_OFF = 1, PAM_PROMPT_ECHO_ON = 2, PAM_ERROR_MSG = 3, PAM_TEXT_INFO = 4
};

#define PAM_CONSTANT(name, value) \
LEAN_EXPORT uint32_t lean_pam_const_##name(b_lean_obj_arg unit) { \
    (void)unit; return (uint32_t)(value); \
}
PAM_CONSTANT(ECHO, ECHO)
PAM_CONSTANT(ECHONL, ECHONL)
PAM_CONSTANT(ICANON, ICANON)
PAM_CONSTANT(IEXTEN, IEXTEN)
PAM_CONSTANT(VMIN, VMIN)
PAM_CONSTANT(VTIME, VTIME)
PAM_CONSTANT(VERASE, VERASE)
PAM_CONSTANT(VKILL, VKILL)
PAM_CONSTANT(VEOF, VEOF)
PAM_CONSTANT(TCSANOW, TCSANOW)
PAM_CONSTANT(TCSADRAIN, TCSADRAIN)
PAM_CONSTANT(PAM_SUCCESS, PAM_SUCCESS)
PAM_CONSTANT(PAM_BUF_ERR, PAM_BUF_ERR)
PAM_CONSTANT(PAM_AUTH_ERR, PAM_AUTH_ERR)
PAM_CONSTANT(PAM_CONV_ERR, PAM_CONV_ERR)
PAM_CONSTANT(PAM_SILENT, PAM_SILENT)
PAM_CONSTANT(PAM_CHANGE_EXPIRED_AUTHTOK, PAM_CHANGE_EXPIRED_AUTHTOK)
PAM_CONSTANT(PAM_REINITIALIZE_CRED, PAM_REINITIALIZE_CRED)
PAM_CONSTANT(PAM_DELETE_CRED, PAM_DELETE_CRED)
PAM_CONSTANT(PAM_TTY, PAM_TTY)
PAM_CONSTANT(PAM_RUSER, PAM_RUSER)
PAM_CONSTANT(PAM_RHOST, PAM_RHOST)
PAM_CONSTANT(PAM_USER, PAM_USER)
PAM_CONSTANT(PAM_PROMPT_ECHO_OFF, PAM_PROMPT_ECHO_OFF)
PAM_CONSTANT(PAM_PROMPT_ECHO_ON, PAM_PROMPT_ECHO_ON)
PAM_CONSTANT(PAM_ERROR_MSG, PAM_ERROR_MSG)
PAM_CONSTANT(PAM_TEXT_INFO, PAM_TEXT_INFO)
PAM_CONSTANT(SUDO_CONV_PROMPT_MASK, SUDO_CONV_PROMPT_MASK)
PAM_CONSTANT(SUDO_CONV_PROMPT_ECHO_OK, SUDO_CONV_PROMPT_ECHO_OK)
PAM_CONSTANT(SUDO_CONV_PROMPT_ECHO_ON, SUDO_CONV_PROMPT_ECHO_ON)
PAM_CONSTANT(SUDO_CONV_TYPE_MASK, 0xff)
PAM_CONSTANT(signalInfoSize, sizeof(struct signalfd_siginfo))
PAM_CONSTANT(invalidFd, -1)
PAM_CONSTANT(POLLIN, POLLIN)
PAM_CONSTANT(callbackSuspendOffset, offsetof(struct sudo_conv_callback, on_suspend))
PAM_CONSTANT(callbackResumeOffset, offsetof(struct sudo_conv_callback, on_resume))
PAM_CONSTANT(callbackClosureOffset, offsetof(struct sudo_conv_callback, closure))

LEAN_EXPORT lean_obj_res lean_pam_sigemptyset(void) {
    lean_object *bytes = lean_alloc_sarray(1, sizeof(sigset_t), sizeof(sigset_t));
    int rc = sigemptyset((sigset_t *)lean_sarray_cptr(bytes));
    if (rc < 0) { int error = errno; lean_dec(bytes);
        return lean_io_result_mk_error(lean_decode_io_error(error, NULL)); }
    return ls_ok(bytes);
}

LEAN_EXPORT lean_obj_res lean_pam_sigaddset(lean_obj_arg bytes, uint32_t signal) {
    if (lean_sarray_size(bytes) != sizeof(sigset_t)) {
        lean_dec(bytes);
        return lean_io_result_mk_error(lean_decode_io_error(EINVAL, NULL));
    }
    if (!lean_is_exclusive(bytes)) bytes = lean_copy_sarray(bytes, sizeof(sigset_t));
    int rc = sigaddset((sigset_t *)lean_sarray_cptr(bytes), signal);
    if (rc < 0) { int error = errno; lean_dec(bytes);
        return lean_io_result_mk_error(lean_decode_io_error(error, NULL)); }
    return ls_ok(bytes);
}

LEAN_EXPORT lean_obj_res lean_pam_read_signal(uint32_t fd) {
    struct signalfd_siginfo info = {0};
    ssize_t rc = read(fd, &info, sizeof info);
    return ls_ok(ls_pair(lean_int_to_int(rc < 0 ? -errno : rc), lean_box_uint32(info.ssi_signo)));
}

LEAN_EXPORT lean_obj_res lean_pam_open(b_lean_obj_arg path, uint32_t flags) {
    int rc = open(lean_string_cstr(path), flags);
    return ls_ok(lean_int_to_int(rc < 0 ? -errno : rc));
}

LEAN_EXPORT lean_obj_res lean_pam_close(uint32_t fd) {
    int rc = close(fd);
    return ls_ok(lean_int_to_int(rc < 0 ? -errno : rc));
}

LEAN_EXPORT lean_obj_res lean_pam_read(uint32_t fd, uint32_t size) {
    lean_object *bytes = lean_alloc_sarray(1, size, size);
    ssize_t rc = read(fd, lean_sarray_cptr(bytes), size);
    int error = errno;
    if (rc < 0) { lean_dec(bytes); return ls_ok(ls_pair(lean_int_to_int(-error),
        lean_alloc_sarray(1, 0, 0))); }
    lean_sarray_set_size(bytes, rc);
    return ls_ok(ls_pair(lean_int_to_int(rc), bytes));
}

LEAN_EXPORT lean_obj_res lean_pam_write(uint32_t fd, b_lean_obj_arg bytes, uint32_t offset) {
    if (offset > lean_sarray_size(bytes)) return ls_ok(lean_int_to_int(-EINVAL));
    ssize_t rc = write(fd, lean_sarray_cptr(bytes) + offset, lean_sarray_size(bytes) - offset);
    return ls_ok(lean_int_to_int(rc < 0 ? -errno : rc));
}

LEAN_EXPORT lean_obj_res lean_pam_poll(uint32_t fd, uint32_t signal_fd,
        uint32_t events, uint32_t timeout) {
    struct pollfd fds[2] = {{.fd = fd, .events = events},
        {.fd = signal_fd, .events = events}};
    int rc = poll(fds, 2, (int32_t)timeout);
    return ls_ok(ls_pair(lean_int_to_int(rc < 0 ? -errno : rc),
        ls_pair(lean_box_uint32(fds[0].revents), lean_box_uint32(fds[1].revents))));
}

LEAN_EXPORT lean_obj_res lean_pam_tcgetattr(uint32_t fd) {
    lean_object *bytes = lean_alloc_sarray(1, sizeof(struct termios), sizeof(struct termios));
    int rc = tcgetattr(fd, (struct termios *)lean_sarray_cptr(bytes));
    return ls_ok(ls_pair(lean_int_to_int(rc < 0 ? -errno : rc), bytes));
}

LEAN_EXPORT lean_obj_res lean_pam_tcsetattr(uint32_t fd, uint32_t action, b_lean_obj_arg bytes) {
    if (lean_sarray_size(bytes) != sizeof(struct termios))
        return ls_ok(lean_int_to_int(-EINVAL));
    int rc = tcsetattr(fd, action, (const struct termios *)lean_sarray_cptr(bytes));
    return ls_ok(lean_int_to_int(rc < 0 ? -errno : rc));
}

LEAN_EXPORT lean_obj_res lean_pam_termios_lflag(b_lean_obj_arg bytes) {
    if (lean_sarray_size(bytes) != sizeof(struct termios))
        return lean_io_result_mk_error(lean_decode_io_error(EINVAL, NULL));
    return ls_ok(lean_box_uint32(((const struct termios *)lean_sarray_cptr(bytes))->c_lflag));
}

LEAN_EXPORT lean_obj_res lean_pam_termios_set_lflag(lean_obj_arg bytes, uint32_t value) {
    if (lean_sarray_size(bytes) != sizeof(struct termios)) {
        lean_dec(bytes);
        return lean_io_result_mk_error(lean_decode_io_error(EINVAL, NULL));
    }
    if (!lean_is_exclusive(bytes)) bytes = lean_copy_sarray(bytes, sizeof(struct termios));
    ((struct termios *)lean_sarray_cptr(bytes))->c_lflag = value;
    return ls_ok(bytes);
}

LEAN_EXPORT lean_obj_res lean_pam_termios_cc(b_lean_obj_arg bytes, uint32_t index) {
    if (lean_sarray_size(bytes) != sizeof(struct termios) || index >= NCCS)
        return lean_io_result_mk_error(lean_decode_io_error(EINVAL, NULL));
    return ls_ok(lean_box_uint32(((const struct termios *)lean_sarray_cptr(bytes))->c_cc[index]));
}

LEAN_EXPORT lean_obj_res lean_pam_termios_set_cc(lean_obj_arg bytes,
        uint32_t index, uint32_t value) {
    if (lean_sarray_size(bytes) != sizeof(struct termios) || index >= NCCS) {
        lean_dec(bytes);
        return lean_io_result_mk_error(lean_decode_io_error(EINVAL, NULL));
    }
    if (!lean_is_exclusive(bytes)) bytes = lean_copy_sarray(bytes, sizeof(struct termios));
    ((struct termios *)lean_sarray_cptr(bytes))->c_cc[index] = value;
    return ls_ok(bytes);
}

LEAN_EXPORT lean_obj_res lean_pam_sigmask(uint32_t action, b_lean_obj_arg bytes) {
    if (lean_sarray_size(bytes) != sizeof(sigset_t))
        return ls_ok(ls_pair(lean_int_to_int(-EINVAL), lean_alloc_sarray(1, 0, 0)));
    sigset_t old;
    int rc = sigprocmask(action, (const sigset_t *)lean_sarray_cptr(bytes), &old);
    int error = errno;
    lean_object *result = lean_alloc_sarray(1, sizeof old, sizeof old);
    if (rc == 0) memcpy(lean_sarray_cptr(result), &old, sizeof old);
    return ls_ok(ls_pair(lean_int_to_int(rc < 0 ? -error : rc), result));
}

LEAN_EXPORT lean_obj_res lean_pam_signalfd(b_lean_obj_arg bytes) {
    if (lean_sarray_size(bytes) != sizeof(sigset_t)) return ls_ok(lean_int_to_int(-EINVAL));
    int rc = signalfd(-1, (const sigset_t *)lean_sarray_cptr(bytes), SFD_CLOEXEC | SFD_NONBLOCK);
    return ls_ok(lean_int_to_int(rc < 0 ? -errno : rc));
}

LEAN_EXPORT lean_obj_res lean_pam_kill(uint32_t pid, uint32_t sig) {
    int rc = kill(pid, sig);
    return ls_ok(lean_int_to_int(rc < 0 ? -errno : rc));
}

LEAN_EXPORT lean_obj_res lean_pam_getpid(void) {
    return ls_ok(lean_box_uint32(getpid()));
}

LEAN_EXPORT lean_obj_res lean_pam_dgettext(b_lean_obj_arg text) {
    const char *message = dgettext("Linux-PAM", lean_string_cstr(text));
    size_t size = strlen(message);
    lean_object *bytes = lean_alloc_sarray(1, size, size);
    memcpy(lean_sarray_cptr(bytes), message, size);
    return ls_ok(bytes);
}

LEAN_EXPORT lean_obj_res lean_pam_callback_call(size_t fn, uint32_t sig, size_t closure) {
    int (*call)(int, void *) = (void *)fn;
    return ls_ok(lean_int_to_int(call(sig, (void *)closure)));
}

struct pam_message { int msg_style; const char *msg; };
struct pam_response { char *resp; int resp_retcode; };
struct pam_conv {
    int (*conv)(int, const struct pam_message **, struct pam_response **, void *);
    void *appdata_ptr;
};
typedef struct {
    void *pamh;
    lean_object *callback;
    struct pam_conv conv;
} pam_context;

PAM_CONSTANT(messageTypeOffset, offsetof(struct pam_message, msg_style))
PAM_CONSTANT(messageTextOffset, offsetof(struct pam_message, msg))
PAM_CONSTANT(responseSize, sizeof(struct pam_response))
PAM_CONSTANT(responseTextOffset, offsetof(struct pam_response, resp))

static int pam_conversation(int count, const struct pam_message **messages,
        struct pam_response **answers, void *data) {
    pam_context *context = data;
    lean_inc(context->callback);
    lean_object *result = lean_apply_4(context->callback, lean_box_uint32(count),
        lean_box_usize((size_t)messages), lean_box_usize((size_t)answers), lean_io_mk_world());
    int status = lean_unbox_uint32(result);
    lean_dec(result);
    return status;
}

static void pam_context_finalize(void *data) {
    pam_context *context = data;
    lean_dec(context->callback);
    free(context);
}

static void pam_context_foreach(void *data, b_lean_obj_arg visit) {
    pam_context *context = data;
    lean_inc(visit);
    lean_inc(context->callback);
    lean_dec(lean_apply_1(visit, context->callback));
}

LEAN_EXPORT lean_obj_res lean_pam_context(lean_obj_arg callback) {
    static lean_external_class *class;
    if (!class) class = lean_register_external_class(pam_context_finalize, pam_context_foreach);
    pam_context *context = calloc(1, sizeof *context);
    if (!context) { lean_dec(callback);
        return lean_io_result_mk_error(lean_decode_io_error(ENOMEM, NULL)); }
    context->callback = callback;
    context->conv = (struct pam_conv){pam_conversation, context};
    return ls_ok(lean_alloc_external(class, context));
}

LEAN_EXPORT lean_obj_res lean_pam_start(size_t fn, b_lean_obj_arg native,
        b_lean_obj_arg service, b_lean_obj_arg user) {
    pam_context *context = lean_get_external_data(native);
    int (*call)(const char *, const char *, const struct pam_conv *, void **) = (void *)fn;
    int rc = call(lean_string_cstr(service), lean_string_cstr(user),
        &context->conv, &context->pamh);
    return ls_ok(lean_int_to_int(rc));
}

LEAN_EXPORT lean_obj_res lean_pam_call(size_t fn, b_lean_obj_arg native, uint32_t flags) {
    pam_context *context = lean_get_external_data(native);
    int (*call)(void *, int) = (void *)fn;
    int rc = call(context->pamh, flags);
    return ls_ok(lean_int_to_int(rc));
}

LEAN_EXPORT lean_obj_res lean_pam_set_item(size_t fn, b_lean_obj_arg native,
        uint32_t item, b_lean_obj_arg value) {
    pam_context *context = lean_get_external_data(native);
    int (*call)(void *, int, const void *) = (void *)fn;
    int rc = call(context->pamh, item, lean_string_cstr(value));
    return ls_ok(lean_int_to_int(rc));
}

LEAN_EXPORT lean_obj_res lean_pam_get_item(size_t fn, b_lean_obj_arg native, uint32_t item) {
    pam_context *context = lean_get_external_data(native);
    int (*call)(const void *, int, const void **) = (void *)fn;
    const void *text = NULL;
    int rc = call(context->pamh, item, &text);
    lean_object *value = lean_box(0);
    if (text) {
        value = lean_alloc_ctor(1, 1, 0);
        size_t size = strlen(text);
        lean_object *bytes = lean_alloc_sarray(1, size, size);
        memcpy(lean_sarray_cptr(bytes), text, size);
        lean_ctor_set(value, 0, bytes);
    }
    return ls_ok(ls_pair(lean_int_to_int(rc), value));
}

LEAN_EXPORT lean_obj_res lean_pam_environment(size_t fn, b_lean_obj_arg native) {
    pam_context *context = lean_get_external_data(native);
    char **(*call)(void *) = (void *)fn;
    return ls_ok(lean_box_usize((size_t)call(context->pamh)));
}

LEAN_EXPORT lean_obj_res lean_pam_strerror(size_t fn, b_lean_obj_arg native, uint32_t code) {
    pam_context *context = lean_get_external_data(native);
    const char *(*call)(void *, int) = (void *)fn;
    return ls_ok(lean_box_usize((size_t)call(context->pamh, code)));
}

LEAN_EXPORT lean_obj_res lean_pam_handle_pointer(b_lean_obj_arg native) {
    pam_context *context = lean_get_external_data(native);
    return ls_ok(lean_box_usize((size_t)context->pamh));
}

LEAN_EXPORT lean_obj_res lean_pam_end(size_t fn, b_lean_obj_arg native, uint32_t status) {
    pam_context *context = lean_get_external_data(native);
    int (*call)(void *, int) = (void *)fn;
    int rc = call(context->pamh, status);
    context->pamh = NULL;
    return ls_ok(lean_int_to_int(rc));
}

LEAN_EXPORT lean_obj_res lean_pam_chdir(b_lean_obj_arg path) {
    int rc = chdir(lean_string_cstr(path));
    return ls_ok(lean_int_to_int(rc < 0 ? -errno : rc));
}

LEAN_EXPORT lean_obj_res lean_pam_exec_inherited(b_lean_obj_arg path, size_t args) {
    extern char **environ;
    int rc = execve(lean_string_cstr(path), (char *const *)args, environ);
    return ls_ok(lean_int_to_int(rc < 0 ? -errno : rc));
}
