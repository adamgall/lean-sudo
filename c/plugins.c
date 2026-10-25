/*
 * Non-policy plugin host. ABI sequencing follows sudo 1.9.17p2 sudo.c,
 * load_plugins.c and exec_iolog.c, Copyright (c) 2009-2024 Todd C. Miller.
 * Permission to use, copy, modify, and distribute this software for any
 * purpose with or without fee is hereby granted, provided that the above
 * copyright notice and this permission notice appear in all copies.
 * THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 * WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
 * ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 * WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
 * ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
 * OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 */
#include <lean/lean.h>
#include "plugins.h"
#include <dlfcn.h>
#include <errno.h>
#include <fcntl.h>
#include <grp.h>
#include <limits.h>
#include <pwd.h>
#include <signal.h>
#include <stdarg.h>
#include <stdatomic.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/ioctl.h>
#include <sys/resource.h>
#include <sys/stat.h>
#include <time.h>
#include <sys/socket.h>
#include <unistd.h>

struct generic_plugin { unsigned type, version; };
typedef int (*conv_old_t)(int, const struct sudo_conv_message *, struct sudo_conv_reply *);
struct io_old {
    unsigned type, version;
    int (*open)(unsigned, conv_old_t, sudo_printf_t, char *const *, char *const *,
        int, char *const *, char *const *);
    void (*close)(int, int);
    int (*show_version)(int);
    int (*ttyin)(const char *, unsigned);
    int (*ttyout)(const char *, unsigned);
    int (*in)(const char *, unsigned);
    int (*out)(const char *, unsigned);
    int (*err)(const char *, unsigned);
};
typedef int (*io_open_1_t)(unsigned, conv_old_t, sudo_printf_t, char *const *,
    char *const *, char *const *, int, char *const *, char *const *);
typedef int (*io_open_2_t)(unsigned, sudo_conv_t, sudo_printf_t, char *const *,
    char *const *, char *const *, int, char *const *, char *const *, char *const *);
struct plugin {
    struct plugin *next;
    void *handle;
    struct generic_plugin *abi;
    char *name, *path;
    char **options, **settings;
    bool opened, disabled;
    unsigned disabled_streams;
    uint32_t line;
};
static struct plugin *plugins, **plugin_tail = &plugins;
static char **settings, **user_info, **submit_argv, **submit_env;
static char **command_info, **run_argv, **run_env;
static bool conv_stdin, conv_noninteractive;
static int submit_optind;
static int native_type, native_status;
static bool native_valid;
static int register_hook(struct sudo_hook *);
static int deregister_hook(struct sudo_hook *);
static struct sudo_plugin_event *event_alloc(void);
static void events_free(void);
static void hooks_free(void);

static int bridge_server = -1, bridge_client = -1;
static pid_t bridge_owner;
/* Remains set after transport failure: a forked broker must never fall back
 * to callbacks against its stale private copy of the host's plugin state. */
static bool bridge_child_mode;
static int bridge_dispatch(void);
static lean_obj_res bridge_request(unsigned op, char **info, char **argv, char **env);
static lean_obj_res ok(void) { return lean_io_result_mk_ok(lean_box(0)); }
static lean_obj_res error(const char *s) {
    return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(s)));
}
static lean_obj_res boolean(bool b) { return lean_io_result_mk_ok(lean_box(b)); }
static void warnx(const char *fmt, ...) {
    va_list ap;
    va_start(ap, fmt);
    fputs("sudo: ", stderr);
    vfprintf(stderr, fmt, ap);
    fputc('\n', stderr);
    va_end(ap);
}
static void free_vector(char **v) {
    if (v) { for (size_t i = 0; v[i]; i++) free(v[i]); free(v); }
}
static char **copy_array(b_lean_obj_arg arr) {
    size_t n = lean_array_size(arr);
    char **v = calloc(n + 1, sizeof(*v));
    if (!v) return NULL;
    for (size_t i = 0; i < n; i++) {
        b_lean_obj_arg s = lean_array_get_core(arr, i);
        if (memchr(lean_string_cstr(s), 0, lean_string_size(s) - 1)) {
            errno = EINVAL; free_vector(v); return NULL;
        }
        if (!(v[i] = strdup(lean_string_cstr(s)))) { free_vector(v); return NULL; }
    }
    return v;
}
static size_t vector_len(char *const *v) {
    size_t n = 0; if (v) while (v[n]) n++; return n;
}
static int plugin_printf(int type, const char *restrict fmt, ...) {
    int fd = -1, ret;
    FILE *out = (type & 0xff) == SUDO_CONV_ERROR_MSG ? stderr : stdout;
    if ((type & 0xff) != SUDO_CONV_ERROR_MSG && (type & 0xff) != SUDO_CONV_INFO_MSG) {
        errno = EINVAL; return -1;
    }
    if (type & SUDO_CONV_PREFER_TTY) fd = open("/dev/tty", O_WRONLY | O_CLOEXEC);
    va_list ap; va_start(ap, fmt);
    ret = fd >= 0 ? vdprintf(fd, fmt, ap) : vfprintf(out, fmt, ap);
    va_end(ap);
    if (fd >= 0) close(fd); else fflush(out);
    return ret;
}
static bool setting_true(const char *name) {
    for (size_t i = 0; settings && settings[i]; i++)
        if (!strcmp(settings[i], name)) return true;
    return false;
}
static int conversation(int n, const struct sudo_conv_message msgs[],
    struct sudo_conv_reply replies[], struct sudo_conv_callback *cb) {
    if (n < 0 || (n && !msgs)) { errno = EINVAL; return -1; }
    if (replies) for (int i = 0; i < n; i++) replies[i].reply = NULL;
    for (int i = 0; i < n; i++) {
        int type = msgs[i].msg_type & 0xff;
        const char *msg = msgs[i].msg ? msgs[i].msg : "";
        if (type == SUDO_CONV_ERROR_MSG || type == SUDO_CONV_INFO_MSG) {
            if (plugin_printf(msgs[i].msg_type, "%s", msg) < 0) goto bad;
        } else if (type == SUDO_CONV_PROMPT_ECHO_OFF || type == SUDO_CONV_PROMPT_ECHO_ON ||
            type == SUDO_CONV_PROMPT_MASK) {
            char buf[SUDO_CONV_REPL_MAX + 1] = {0};
            if (!replies || conv_noninteractive || setting_true("noninteractive=true")) goto bad;
            int rc = ls_plugin_read_reply(msg, msgs[i].msg_type,
                msgs[i].timeout > 0 ? (unsigned)msgs[i].timeout : 0,
                conv_stdin || setting_true("read_stdin=true"), buf, sizeof buf, cb);
            if (rc == 0) replies[i].reply = strdup(buf);
            explicit_bzero(buf, sizeof buf);
            if (rc != 0 || !replies[i].reply) goto bad;
        } else { errno = EINVAL; goto bad; }
    }
    return 0;
bad:
    if (replies) for (int i = 0; i < n; i++) {
        if (replies[i].reply) {
            explicit_bzero(replies[i].reply, strlen(replies[i].reply));
            free(replies[i].reply); replies[i].reply = NULL;
        }
    }
    return -1;
}
static int conversation_old(int n, const struct sudo_conv_message *m, struct sudo_conv_reply *r) {
    return conversation(n, m, r, NULL);
}
/* This front-end capability probe must not pull the execution/interception
 * broker into visudo merely because libc environment hooks share this object. */
static bool trace_supported(void) {
#if defined(__linux__) && (defined(__aarch64__) || defined(__x86_64__))
    FILE *fp = fopen("/proc/sys/kernel/seccomp/actions_avail", "re");
    if (!fp) return false;
    char actions[512];
    bool supported = false;
    if (fgets(actions, sizeof actions, fp)) {
        char *save;
        for (char *action = strtok_r(actions, " \t\r\n", &save); action;
                action = strtok_r(NULL, " \t\r\n", &save)) {
            if (!strcmp(action, "trap")) { supported = true; break; }
        }
    }
    fclose(fp);
    return supported;
#else
    return false;
#endif
}
static bool format_settings(struct plugin *p) {
    if (p->settings) return true;
    size_t n = vector_len(settings);
    int intercept = trace_supported();
    p->settings = calloc(n + (intercept ? 4 : 2), sizeof(char *));
    if (!p->settings || asprintf(&p->settings[0], "plugin_path=%s", p->path) < 0) return false;
    for (size_t i = 0; i < n; i++) if (!(p->settings[i + 1] = strdup(settings[i]))) return false;
    if (intercept) {
        p->settings[n + 1] = strdup("intercept_setid=true");
        if (!p->settings[n + 1]) return false;
        p->settings[n + 2] = strdup("intercept_ptrace=true");
        if (!p->settings[n + 2]) return false;
    }
    return true;
}
static void plugin_hooks(struct plugin *p, bool add) {
    void (*fn)(int, int (*)(struct sudo_hook *)) = NULL;
    if (p->abi->type == SUDO_IO_PLUGIN && p->abi->version >= SUDO_API_MKVERSION(1, 2)) {
        struct io_plugin *a = (void *)p->abi;
        fn = add ? a->register_hooks : a->deregister_hooks;
    } else if (p->abi->type == SUDO_AUDIT_PLUGIN) {
        struct audit_plugin *a = (void *)p->abi;
        fn = add ? a->register_hooks : a->deregister_hooks;
    }
    if (fn) fn(SUDO_HOOK_VERSION, add ? register_hook : deregister_hook);
}
static void disable(struct plugin *p) {
    plugin_hooks(p, false);
    p->disabled = true;
}
LEAN_EXPORT lean_obj_res lean_sudo_plugins_load(b_lean_obj_arg symbol, b_lean_obj_arg path,
    uint32_t line, b_lean_obj_arg options) {
    const char *name = lean_string_cstr(symbol), *file = lean_string_cstr(path);
    void *handle = dlopen(file, RTLD_LAZY | RTLD_GLOBAL);
    if (!handle) {
        const char *why = dlerror();
        warnx("error in /etc/sudo.conf, line %u while loading plugin \"%s\"", line, name);
        warnx("unable to load %s: %s", file, why ? why : "unknown error");
        return error("fatal error, unable to load plugins");
    }
    struct generic_plugin *abi = dlsym(handle, name);
    if (!abi) {
        warnx("error in /etc/sudo.conf, line %u while loading plugin \"%s\"", line, name);
        warnx("unable to find symbol \"%s\" in %s", name, file); goto bad;
    }
    if (SUDO_API_VERSION_GET_MAJOR(abi->version) != SUDO_API_VERSION_MAJOR) {
        warnx("error in /etc/sudo.conf, line %u while loading plugin \"%s\"", line, name);
        warnx("incompatible plugin major version %u (expected %u) found in %s",
            SUDO_API_VERSION_GET_MAJOR(abi->version), SUDO_API_VERSION_MAJOR, file); goto bad;
    }
    if (abi->type < SUDO_IO_PLUGIN || abi->type > SUDO_APPROVAL_PLUGIN) {
        warnx("error in /etc/sudo.conf, line %u while loading plugin \"%s\"", line, name);
        if (abi->type == SUDO_POLICY_PLUGIN)
            warnx("policy plugin %s is not supported; policy is implemented by Lean", name);
        else warnx("unknown plugin type %u found in %s", abi->type, file);
        goto bad;
    }
    for (struct plugin *p = plugins; p; p = p->next) {
        if (p->abi->type != abi->type || strcmp(p->name, name)) continue;
        char *clone_name;
        if (asprintf(&clone_name, "%s_clone", name) < 0) goto oom;
        struct generic_plugin *(*clone)(void) = (void *)dlsym(handle, clone_name);
        free(clone_name);
        struct generic_plugin *copy = clone ? clone() : NULL;
        if (!copy) {
            warnx("ignoring duplicate plugin \"%s\" in /etc/sudo.conf, line %u", name, line);
            dlclose(handle); return ok();
        }
        if (copy->type != abi->type || SUDO_API_VERSION_GET_MAJOR(copy->version) != 1) {
            warnx("incompatible cloned plugin %s", name); goto bad;
        }
        abi = copy; break;
    }
    struct plugin *p = calloc(1, sizeof(*p));
    if (!p) goto oom;
    p->handle = handle; p->abi = abi;
    p->line = line;
    p->name = strdup(name); p->path = strdup(file);
    if (lean_array_size(options)) p->options = copy_array(options);
    if (!p->name || !p->path || (lean_array_size(options) && !p->options)) {
        free(p->name); free(p->path); free_vector(p->options); free(p); goto oom;
    }
    if (abi->type == SUDO_IO_PLUGIN && abi->version >= SUDO_API_MKVERSION(1, 15))
        ((struct io_plugin *)abi)->event_alloc = event_alloc;
    if (abi->type == SUDO_AUDIT_PLUGIN && abi->version >= SUDO_API_MKVERSION(1, 17))
        ((struct audit_plugin *)abi)->event_alloc = event_alloc;
    *plugin_tail = p; plugin_tail = &p->next;
    plugin_hooks(p, true);
    return ok();
oom:
    warnx("unable to allocate memory");
bad:
    dlclose(handle); return error("fatal error, unable to load plugins");
}
static bool audit_message(struct plugin *source, const char *name, unsigned type,
    const char *msg, char *const *info, bool is_error) {
    bool success = true;
    for (struct plugin *p = plugins; p; p = p->next) {
        if (p == source || p->disabled || !p->opened || p->abi->type != SUDO_AUDIT_PLUGIN) continue;
        struct audit_plugin *a = (void *)p->abi;
        int (*fn)(const char *, unsigned, const char *, char *const *, const char **) =
            is_error ? a->error : a->reject;
        const char *why = NULL;
        if (fn && fn(name, type, msg, info, &why) != 1) {
            warnx("%s: unable to log %s event%s%s", p->name, is_error ? "error" : "reject",
                why ? ": " : "", why ? why : "");
            success = false;
            if (!is_error) {
                audit_message(p, p->name, SUDO_AUDIT_PLUGIN,
                    why ? why : "audit plugin error", info, true);
                break;
            }
        }
    }
    return success;
}
static bool audit_accept(const char *name, unsigned type, char *const *info,
    char *const *argv, char *const *env) {
    for (struct plugin *p = plugins; p; p = p->next) {
        if (p->disabled || !p->opened || p->abi->type != SUDO_AUDIT_PLUGIN) continue;
        struct audit_plugin *a = (void *)p->abi;
        const char *why = NULL;
        if (a->accept && a->accept(name, type, info, argv, env, &why) != 1) {
            warnx("%s: unable to log accept event%s%s", p->name, why ? ": " : "", why ? why : "");
            audit_message(p, p->name, SUDO_AUDIT_PLUGIN,
                why ? why : "audit plugin error", info, true);
            return false;
        }
    }
    return true;
}
static int open_plugin(struct plugin *p, bool version, const char **why) {
    if (!format_settings(p)) { *why = "unable to allocate memory"; return -1; }
    unsigned type = p->abi->type, v = p->abi->version;
    int argc = version ? 0 : (int)vector_len(run_argv);
    char **info = version ? NULL : command_info;
    char **argv = version ? submit_argv : run_argv;
    char **env = version ? submit_env : run_env;
    if (type == SUDO_AUDIT_PLUGIN) {
        struct audit_plugin *a = (void *)p->abi;
        if (!a->open) { *why = "missing open method"; return -1; }
        return a->open(SUDO_API_VERSION, conversation, plugin_printf, p->settings,
            user_info, submit_optind, submit_argv, submit_env, p->options, why);
    }
    if (type == SUDO_APPROVAL_PLUGIN) {
        struct approval_plugin *a = (void *)p->abi;
        if (!a->open) { *why = "missing open method"; return -1; }
        return a->open(SUDO_API_VERSION, conversation, plugin_printf, p->settings,
            user_info, submit_optind, submit_argv, submit_env, p->options, why);
    }
    struct io_plugin *a = (void *)p->abi;
    if (!a->open) { *why = "missing open method"; return -1; }
    if (v == SUDO_API_MKVERSION(1, 0))
        return ((struct io_old *)a)->open(v, conversation_old, plugin_printf,
            p->settings, user_info, argc, argv, env);
    if (v == SUDO_API_MKVERSION(1, 1)) {
        io_open_1_t open_old;
        memcpy(&open_old, &a->open, sizeof open_old);
        return open_old(v, conversation_old, plugin_printf,
            p->settings, user_info, info, argc, argv, env);
    }
    if (v < SUDO_API_MKVERSION(1, 15)) {
        io_open_2_t open_old;
        memcpy(&open_old, &a->open, sizeof open_old);
        return open_old(SUDO_API_VERSION, conversation, plugin_printf,
            p->settings, user_info, info, argc, argv, env, p->options);
    }
    return a->open(SUDO_API_VERSION, conversation, plugin_printf, p->settings,
        user_info, info, argc, argv, env, p->options, why);
}
LEAN_EXPORT lean_obj_res lean_sudo_plugins_open(b_lean_obj_arg s, b_lean_obj_arg u,
    b_lean_obj_arg av, b_lean_obj_arg ev, uint32_t optind) {
    if (settings) return error("plugins already opened");
    settings = copy_array(s); user_info = copy_array(u);
    submit_argv = copy_array(av); submit_env = copy_array(ev);
    if (!settings || !user_info || !submit_argv || !submit_env) return error("unable to allocate plugin context");
    if (optind > INT_MAX) return error("invalid submit argument index");
    submit_optind = (int)optind;
    for (struct plugin *p = plugins; p; p = p->next) {
        if (p->disabled || p->abi->type != SUDO_AUDIT_PLUGIN) continue;
        const char *why = NULL;
        int rc = open_plugin(p, false, &why);
        if (rc == 1) p->opened = true;
        else if (rc == 0) disable(p);
        else if (rc == -2) return error("plugin requested usage");
        else {
            char msg[512]; snprintf(msg, sizeof msg, "error initializing audit plugin %s", p->name);
            return error(msg);
        }
    }
    return ok();
}
static bool command_context(b_lean_obj_arg info, b_lean_obj_arg argv, b_lean_obj_arg env) {
    char **i = copy_array(info), **a = copy_array(argv), **e = copy_array(env);
    if (!i || !a || !e) { free_vector(i); free_vector(a); free_vector(e); return false; }
    free_vector(command_info); free_vector(run_argv); free_vector(run_env);
    command_info = i; run_argv = a; run_env = e;
    return true;
}
LEAN_EXPORT lean_obj_res lean_sudo_plugins_accept(b_lean_obj_arg info, b_lean_obj_arg argv, b_lean_obj_arg env) {
    if (!command_context(info, argv, env)) return error("unable to allocate plugin context");
    (void)audit_accept("sudoers_policy", SUDO_POLICY_PLUGIN, command_info, run_argv, run_env);
    return boolean(true); /* sudo.c ignores audit failure for list/validate. */
}
static lean_obj_res check_current(bool initial, bool enforce) {
    if (enforce) {
        bool accepted = audit_accept("sudoers_policy", SUDO_POLICY_PLUGIN,
            command_info, run_argv, run_env);
        if (initial && !accepted) return boolean(false);
    }
    for (struct plugin *p = enforce ? plugins : NULL; p; p = p->next) {
        if (p->disabled || p->abi->type != SUDO_APPROVAL_PLUGIN) continue;
        struct approval_plugin *a = (void *)p->abi;
        if (!a->check) continue;
        const char *why = NULL;
        int rc = open_plugin(p, false, &why);
        if (rc == 0) { disable(p); continue; }
        if (rc == -2) return error("plugin requested usage");
        if (rc != 1) {
            warnx("error initializing approval plugin %s", p->name); return boolean(false);
        }
        rc = a->check(command_info, run_argv, run_env, &why);
        if (rc == 1) {
            if (!audit_accept(p->name, SUDO_APPROVAL_PLUGIN, command_info, run_argv, run_env)) rc = -1;
        } else if (rc != -2) audit_message(NULL, p->name, SUDO_APPROVAL_PLUGIN,
            why ? why : rc == 0 ? "command rejected by approver" : "approval plugin error",
            command_info, rc != 0);
        if (a->close) a->close();
        if (rc == -2) return error("plugin requested usage");
        if (rc != 1) return boolean(false);
    }
    for (struct plugin *p = initial ? plugins : NULL; p; p = p->next) {
        if (p->disabled || p->abi->type != SUDO_IO_PLUGIN) continue;
        const char *why = NULL;
        int rc = open_plugin(p, false, &why);
        if (rc == 1) p->opened = true;
        else if (rc == 0) disable(p);
        else if (rc == -2) return error("plugin requested usage");
        else {
            warnx("error initializing I/O plugin %s", p->name);
            audit_message(NULL, p->name, SUDO_IO_PLUGIN,
                why ? why : "error initializing I/O plugin", command_info, true);
            return boolean(false);
        }
    }
    bool accepted = audit_accept("sudo", SUDO_FRONT_END, command_info, run_argv, run_env);
    /* exec_intercept.c treats policy/front-end audit as notification, unlike
     * initial execution. approval_check still acts on its own audit result. */
    return boolean(!initial || accepted);
}
LEAN_EXPORT lean_obj_res lean_sudo_plugins_check(b_lean_obj_arg info, b_lean_obj_arg argv, b_lean_obj_arg env) {
    if (!command_context(info, argv, env)) return error("unable to allocate plugin context");
    return check_current(true, true);
}

/* Subcommand callbacks must not free the vectors retained by an open I/O
 * plugin, nor reopen that plugin. Log-only checks retain the initial metadata
 * except for the actual command and working directory. */
static lean_obj_res check_subcommand(char **info, char **argv, char **env, bool enforce) {
    if (!enforce) {
        size_t n = vector_len(command_info), extra = vector_len(info), used = 0;
        char **merged = calloc(n + extra + 1, sizeof(*merged));
        if (!merged) goto failed;
        for (size_t i = 0; i < n; i++) {
            if (!strncmp(command_info[i], "command=", 8) || !strncmp(command_info[i], "runcwd=", 7)) continue;
            if (!(merged[used++] = strdup(command_info[i]))) { free_vector(merged); goto failed; }
        }
        for (size_t i = 0; i < extra; i++) {
            if (!(merged[used++] = strdup(info[i]))) { free_vector(merged); goto failed; }
        }
        free_vector(info); info = merged;
    }
    char **saved_info = command_info, **saved_argv = run_argv, **saved_env = run_env;
    command_info = info; run_argv = argv; run_env = env;
    lean_object *result = check_current(false, enforce);
    command_info = saved_info; run_argv = saved_argv; run_env = saved_env;
    free_vector(info); free_vector(argv); free_vector(env);
    return result;
failed:
    free_vector(info); free_vector(argv); free_vector(env);
    return error("unable to allocate plugin context");
}

LEAN_EXPORT lean_obj_res lean_sudo_plugins_check_subcommand(b_lean_obj_arg info,
    b_lean_obj_arg argv, b_lean_obj_arg env, uint8_t enforce) {
    if (bridge_child_mode && bridge_client < 0)
        return error("unable to check intercepted command with plugins");
    if (!plugins) return boolean(true);
    char **i = copy_array(info), **a = copy_array(argv), **e = copy_array(env);
    if (!i || !a || !e) {
        free_vector(i); free_vector(a); free_vector(e);
        return error("unable to allocate plugin context");
    }
    if (bridge_client >= 0) {
        lean_object *result = bridge_request(enforce ? 1 : 2, i, a, e);
        free_vector(i); free_vector(a); free_vector(e);
        return result;
    }
    return check_subcommand(i, a, e, enforce != 0);
}
LEAN_EXPORT lean_obj_res lean_sudo_plugins_reject(b_lean_obj_arg message, uint8_t is_error,
    b_lean_obj_arg info) {
    if (bridge_child_mode && bridge_client < 0)
        return error("unable to check intercepted command with plugins");
    char **v = copy_array(info);
    if (!v) return error("unable to allocate plugin context");
    if (bridge_client >= 0) {
        char *message_vector[] = {(char *)lean_string_cstr(message), NULL};
        char *empty[] = {NULL};
        lean_object *result = bridge_request(is_error ? 4 : 3, v, message_vector, empty);
        free_vector(v);
        if (lean_io_result_is_ok(result)) {
            bool accepted = lean_unbox(lean_io_result_get_value(result)) == 1;
            lean_dec(result);
            return accepted ? ok() : error("unable to log policy event");
        }
        return result;
    }
    bool rc = audit_message(NULL, "sudoers_policy", SUDO_POLICY_PLUGIN,
        lean_string_cstr(message), v, is_error);
    free_vector(v);
    return rc ? ok() : error("unable to log policy event");
}

/* The Lean interception broker is forked, but plugin state belongs to the
 * original privileged host. A private CLOEXEC socket carries callback data
 * and an affirmative result back; missing/malformed replies never authorize. */
void ls_plugins_broker_close(void) {
    if (bridge_server >= 0) close(bridge_server);
    if (bridge_client >= 0) close(bridge_client);
    bridge_server = bridge_client = -1;
    bridge_owner = 0;
}
int ls_plugins_broker_init(void) {
    if (!plugins) return 0;
    if (bridge_server >= 0 || bridge_client >= 0) { errno = EBUSY; return -1; }
    int pair[2];
    if (socketpair(AF_UNIX, SOCK_STREAM | SOCK_CLOEXEC, 0, pair)) return -1;
    bridge_server = pair[0]; bridge_client = pair[1]; bridge_owner = getpid();
    return 0;
}
void ls_plugins_broker_child(void) {
    bridge_child_mode = bridge_client >= 0;
    if (bridge_server >= 0) close(bridge_server);
    bridge_server = -1; bridge_owner = 0;
}
void ls_plugins_broker_parent(void) {
    if (bridge_client >= 0) close(bridge_client);
    bridge_client = -1;
}
static int bridge_transfer(int fd, void *data, size_t size, bool writing) {
    char *p = data;
    while (size) {
        ssize_t n = writing ? send(fd, p, size, MSG_NOSIGNAL) : read(fd, p, size);
        if (n < 0 && errno == EINTR) continue;
        if (n <= 0) { if (!n) errno = EPIPE; return -1; }
        p += n; size -= (size_t)n;
    }
    return 0;
}
#define BRIDGE_MAX_BYTES (16U * 1024U * 1024U)
static int bridge_send_vector(int fd, char **v, size_t *remaining) {
    size_t count = vector_len(v);
    if (count > *remaining / sizeof(char *)) { errno = E2BIG; return -1; }
    *remaining -= count * sizeof(char *);
    uint32_t n = (uint32_t)count;
    if (bridge_transfer(fd, &n, sizeof n, true)) return -1;
    for (size_t i = 0; i < count; i++) {
        size_t size = strlen(v[i]) + 1;
        if (size > *remaining) { errno = E2BIG; return -1; }
        *remaining -= size;
        uint32_t bytes = (uint32_t)size;
        if (bridge_transfer(fd, &bytes, sizeof bytes, true) ||
            bridge_transfer(fd, v[i], size, true)) return -1;
    }
    return 0;
}
static char **bridge_receive_vector(int fd, size_t *remaining) {
    uint32_t count;
    if (bridge_transfer(fd, &count, sizeof count, false) ||
        count > *remaining / sizeof(char *)) return NULL;
    *remaining -= (size_t)count * sizeof(char *);
    char **v = calloc((size_t)count + 1, sizeof(*v));
    if (!v) return NULL;
    for (uint32_t i = 0; i < count; i++) {
        uint32_t bytes;
        if (bridge_transfer(fd, &bytes, sizeof bytes, false) || !bytes || bytes > *remaining)
            goto failed;
        *remaining -= bytes;
        v[i] = malloc(bytes);
        if (!v[i] || bridge_transfer(fd, v[i], bytes, false) ||
            v[i][bytes - 1] || memchr(v[i], 0, bytes - 1)) goto failed;
    }
    return v;
failed:
    free_vector(v);
    return NULL;
}
static lean_obj_res bridge_request(unsigned op, char **info, char **argv, char **env) {
    uint32_t operation = op;
    uint8_t answer = 0;
    size_t remaining = BRIDGE_MAX_BYTES;
    if (bridge_transfer(bridge_client, &operation, sizeof operation, true) ||
        bridge_send_vector(bridge_client, info, &remaining) ||
        bridge_send_vector(bridge_client, argv, &remaining) ||
        bridge_send_vector(bridge_client, env, &remaining) ||
        bridge_transfer(bridge_client, &answer, sizeof answer, false) || answer > 1) {
        ls_plugins_broker_close();
        return error("unable to check intercepted command with plugins");
    }
    return boolean(answer == 1);
}
static int bridge_dispatch(void) {
    uint32_t op;
    size_t remaining = BRIDGE_MAX_BYTES;
    char **info = NULL, **argv = NULL, **env = NULL;
    if (bridge_transfer(bridge_server, &op, sizeof op, false) || op < 1 || op > 4 ||
        !(info = bridge_receive_vector(bridge_server, &remaining)) ||
        !(argv = bridge_receive_vector(bridge_server, &remaining)) ||
        !(env = bridge_receive_vector(bridge_server, &remaining))) goto failed;
    uint8_t answer;
    if (op <= 2) {
        lean_object *result = check_subcommand(info, argv, env, op == 1);
        info = argv = env = NULL;
        answer = lean_io_result_is_ok(result) &&
            lean_unbox(lean_io_result_get_value(result)) == 1;
        lean_dec(result);
    } else {
        if (!argv[0] || argv[1] || env[0]) goto failed;
        answer = audit_message(NULL, "sudoers_policy", SUDO_POLICY_PLUGIN,
            argv[0], info, op == 4);
    }
    free_vector(info); free_vector(argv); free_vector(env);
    return bridge_transfer(bridge_server, &answer, sizeof answer, true);
failed:
    free_vector(info); free_vector(argv); free_vector(env);
    ls_plugins_broker_close();
    errno = EIO;
    return -1;
}
LEAN_EXPORT lean_obj_res lean_sudo_plugins_has_io(void) {
    for (struct plugin *p = plugins; p; p = p->next)
        if (!p->disabled && p->abi->type == SUDO_IO_PLUGIN) return boolean(true);
    return boolean(false);
}
LEAN_EXPORT lean_obj_res lean_sudo_plugins_version(uint8_t verbose,
    uint32_t builtin_io_line, uint32_t builtin_audit_line) {
    for (unsigned type = SUDO_IO_PLUGIN; type <= SUDO_APPROVAL_PLUGIN; type += 2) {
        for (struct plugin *p = plugins; p; p = p->next) {
            if (p->disabled || p->abi->type != type) continue;
            if (type == SUDO_IO_PLUGIN && builtin_io_line && builtin_io_line < p->line) {
                plugin_printf(SUDO_CONV_INFO_MSG, "Sudoers I/O plugin version 1.9.17p2\n");
                builtin_io_line = 0;
            }
            const char *why = NULL;
            if (type == SUDO_APPROVAL_PLUGIN && !((struct approval_plugin *)p->abi)->show_version) continue;
            int rc = open_plugin(p, true, &why);
            if (type == SUDO_IO_PLUGIN) {
                struct io_plugin *a = (void *)p->abi;
                if (rc != -1) {
                    if (a->show_version) a->show_version(verbose);
                    if (a->version >= SUDO_API_MKVERSION(1, 15) && a->close) a->close(0, 0);
                }
            } else {
                struct approval_plugin *a = (void *)p->abi;
                if (rc == 0) disable(p);
                else if (rc == 1) { a->show_version(verbose); if (a->close) a->close(); }
                else if (rc == -2) return error("plugin requested usage");
                else return error("error initializing approval plugin");
            }
        }
        if (type == SUDO_IO_PLUGIN && builtin_io_line) {
            plugin_printf(SUDO_CONV_INFO_MSG, "Sudoers I/O plugin version 1.9.17p2\n");
            builtin_io_line = 0;
        }
    }
    for (struct plugin *p = plugins; p; p = p->next) {
        if (p->disabled || !p->opened || p->abi->type != SUDO_AUDIT_PLUGIN) continue;
        if (builtin_audit_line && builtin_audit_line < p->line) {
            plugin_printf(SUDO_CONV_INFO_MSG, "Sudoers audit plugin version 1.9.17p2\n");
            builtin_audit_line = 0;
        }
        struct audit_plugin *a = (void *)p->abi;
        if (a->show_version) a->show_version(verbose);
        if (a->close) a->close(SUDO_PLUGIN_NO_STATUS, 0);
        p->opened = false;
    }
    if (builtin_audit_line)
        plugin_printf(SUDO_CONV_INFO_MSG, "Sudoers audit plugin version 1.9.17p2\n");
    return ok();
}
void ls_plugins_exec_begin(void) {
    native_type = SUDO_PLUGIN_SUDO_ERROR; native_status = 1; native_valid = true;
}
void ls_plugins_exec_status(int type, int status) {
    if (type == SUDO_PLUGIN_SUDO_ERROR && native_valid &&
        (native_type == SUDO_PLUGIN_WAIT_STATUS || native_type == SUDO_PLUGIN_EXEC_ERROR)) return;
    native_type = type; native_status = status; native_valid = true;
}
LEAN_EXPORT lean_obj_res lean_sudo_plugins_close(uint32_t type, uint32_t status) {
    ls_plugins_broker_close();
    if (native_valid) { type = native_type; status = native_status; }
    for (struct plugin *p = plugins; p; p = p->next) {
        if (p->opened && p->abi->type == SUDO_IO_PLUGIN) {
            struct io_plugin *a = (void *)p->abi;
            if (a->close) a->close(type == SUDO_PLUGIN_WAIT_STATUS ? (int)status : 0,
                type == SUDO_PLUGIN_EXEC_ERROR ? (int)status : 0);
            p->opened = false;
        }
    }
    for (struct plugin *p = plugins; p; p = p->next) {
        if (p->opened && p->abi->type == SUDO_AUDIT_PLUGIN) {
            struct audit_plugin *a = (void *)p->abi;
            if (a->close) a->close((int)type, (int)status);
        }
        if (!p->disabled) plugin_hooks(p, false);
    }
    events_free(); hooks_free();
    while (plugins) {
        struct plugin *p = plugins; plugins = p->next;
        free_vector(p->settings); free_vector(p->options);
        free(p->name); free(p->path); dlclose(p->handle); free(p);
    }
    plugin_tail = &plugins;
    free_vector(settings); settings = NULL; free_vector(user_info); user_info = NULL;
    free_vector(submit_argv); submit_argv = NULL; free_vector(submit_env); submit_env = NULL;
    free_vector(command_info); command_info = NULL;
    free_vector(run_argv); run_argv = NULL; free_vector(run_env); run_env = NULL;
    native_valid = false;
    conv_stdin = conv_noninteractive = false;
    ls_plugin_conversation_config(0, NULL);
    return ok();
}
typedef int (*log_fn)(const char *, unsigned, const char **);
static log_fn stream_fn(struct plugin *p, int stream) {
    struct io_plugin *a = (void *)p->abi;
    switch (stream) {
    case 0: return a->log_stdin;
    case 1: return a->log_stdout;
    case 2: return a->log_stderr;
    case 3: return a->log_ttyin;
    case 4: return a->log_ttyout;
    default: return NULL;
    }
}
int ls_plugins_io_stream(int stream) {
    for (struct plugin *p = plugins; p; p = p->next)
        if (p->opened && !p->disabled && p->abi->type == SUDO_IO_PLUGIN &&
            stream >= 0 && stream < 5 && !(p->disabled_streams & (1U << stream)) && stream_fn(p, stream)) return 1;
    return 0;
}
int ls_plugins_io_active(void) {
    for (struct plugin *p = plugins; p; p = p->next)
        if (p->opened && !p->disabled && p->abi->type == SUDO_IO_PLUGIN) return 1;
    return 0;
}
int ls_plugins_io_write(int stream, const void *data, size_t size) {
    if (stream < 0 || stream > 4 || size > UINT_MAX) { errno = EINVAL; return -1; }
    for (struct plugin *p = plugins; p; p = p->next) {
        if (!p->opened || p->disabled || p->abi->type != SUDO_IO_PLUGIN ||
            (p->disabled_streams & (1U << stream))) continue;
        log_fn fn = stream_fn(p, stream);
        if (!fn) continue;
        const char *why = NULL;
        int rc;
        if (p->abi->version < SUDO_API_MKVERSION(1, 15)) {
            int (*log_old)(const char *, unsigned);
            memcpy(&log_old, &fn, sizeof log_old);
            rc = log_old(data, (unsigned)size);
        } else {
            rc = fn(data, (unsigned)size, &why);
        }
        if (rc <= 0) {
            if (rc < 0) p->disabled_streams |= 1U << stream;
            audit_message(NULL, p->name, SUDO_IO_PLUGIN,
                why ? why : rc < 0 ? "I/O plugin error" : "command rejected by I/O plugin",
                command_info, rc < 0);
            errno = EIO; return -1;
        }
    }
    return 0;
}
int ls_plugins_io_winsize(unsigned rows, unsigned cols) {
    for (struct plugin *p = plugins; p; p = p->next) {
        if (!p->opened || p->disabled || p->abi->type != SUDO_IO_PLUGIN ||
            p->abi->version < SUDO_API_MKVERSION(1, 12) || (p->disabled_streams & 32)) continue;
        struct io_plugin *a = (void *)p->abi;
        const char *why = NULL;
        int rc = 1;
        if (a->change_winsize) {
            if (a->version < SUDO_API_MKVERSION(1, 15)) {
                int (*winsize_old)(unsigned, unsigned);
                memcpy(&winsize_old, &a->change_winsize, sizeof winsize_old);
                rc = winsize_old(rows, cols);
            } else {
                rc = a->change_winsize(rows, cols, &why);
            }
        }
        if (rc <= 0) {
            p->disabled_streams |= 32;
            audit_message(NULL, p->name, SUDO_IO_PLUGIN,
                why ? why : "error changing window size", command_info, true);
            errno = EIO; return -1;
        }
    }
    return 0;
}
int ls_plugins_io_suspend(int signo) {
    for (struct plugin *p = plugins; p; p = p->next) {
        if (!p->opened || p->disabled || p->abi->type != SUDO_IO_PLUGIN ||
            p->abi->version < SUDO_API_MKVERSION(1, 13) || (p->disabled_streams & 64)) continue;
        struct io_plugin *a = (void *)p->abi;
        const char *why = NULL;
        int rc = 1;
        if (a->log_suspend) {
            if (a->version < SUDO_API_MKVERSION(1, 15)) {
                int (*suspend_old)(int);
                memcpy(&suspend_old, &a->log_suspend, sizeof suspend_old);
                rc = suspend_old(signo);
            } else {
                rc = a->log_suspend(signo, &why);
            }
        }
        if (rc <= 0) {
            p->disabled_streams |= 64;
            audit_message(NULL, p->name, SUDO_IO_PLUGIN,
                why ? why : "error logging suspend", command_info, true);
            errno = EIO; return -1;
        }
    }
    return 0;
}

/* Environment hooks are process-local, as in sudo's hooks.c. Reentrant libc
 * calls from a hook bypass hooks so providers may inspect the real environment. */
struct env_hook { struct env_hook *next; struct sudo_hook value; };
static struct env_hook *env_hooks;
static _Thread_local unsigned in_hook;
static int register_hook(struct sudo_hook *h) {
    if (!h || SUDO_API_VERSION_GET_MAJOR(h->hook_version) != 1 || !h->hook_fn) {
        errno = EINVAL; return -1;
    }
    if (h->hook_type < SUDO_HOOK_SETENV || h->hook_type > SUDO_HOOK_GETENV) {
        errno = ENOTSUP; return 1;
    }
    struct env_hook *entry = malloc(sizeof(*entry));
    if (!entry) return -1;
    entry->value = *h; entry->next = env_hooks;
    env_hooks = entry;
    return 0;
}
static int deregister_hook(struct sudo_hook *h) {
    if (!h || SUDO_API_VERSION_GET_MAJOR(h->hook_version) != 1) { errno = EINVAL; return -1; }
    if (h->hook_type < SUDO_HOOK_SETENV || h->hook_type > SUDO_HOOK_GETENV) return 1;
    for (struct env_hook **p = &env_hooks; *p; p = &(*p)->next) {
        if ((*p)->value.hook_type == h->hook_type &&
            (*p)->value.hook_fn == h->hook_fn && (*p)->value.closure == h->closure) {
            struct env_hook *old = *p; *p = old->next; free(old); return 0;
        }
    }
    return 0;
}
static void hooks_free(void) {
    while (env_hooks) { struct env_hook *h = env_hooks; env_hooks = h->next; free(h); }
}
char *getenv(const char *name) {
    if (!in_hook) {
        in_hook++;
        for (struct env_hook *h = env_hooks; h; h = h->next) {
            if (h->value.hook_type != SUDO_HOOK_GETENV) continue;
            char *value = NULL;
            int rc = ((sudo_hook_fn_getenv_t)h->value.hook_fn)(name, &value, h->value.closure);
            if (rc != SUDO_HOOK_RET_NEXT) { in_hook--; return rc == SUDO_HOOK_RET_STOP ? value : NULL; }
        }
        in_hook--;
    }
    extern char **environ;
    size_t len = strlen(name);
    if (!len || strchr(name, '=')) return NULL;
    for (char **v = environ; v && *v; v++)
        if (!strncmp(*v, name, len) && (*v)[len] == '=') return *v + len + 1;
    return NULL;
}
int setenv(const char *name, const char *value, int overwrite) {
    static int (*real_setenv)(const char *, const char *, int);
    if (!real_setenv) real_setenv = (void *)dlsym(RTLD_NEXT, "setenv");
    if (!in_hook) {
        in_hook++;
        for (struct env_hook *h = env_hooks; h; h = h->next) {
            if (h->value.hook_type != SUDO_HOOK_SETENV) continue;
            int rc = ((sudo_hook_fn_setenv_t)h->value.hook_fn)(name, value, overwrite, h->value.closure);
            if (rc != SUDO_HOOK_RET_NEXT) { in_hook--; return rc == SUDO_HOOK_RET_STOP ? 0 : -1; }
        }
        in_hook--;
    }
    if (!real_setenv) { errno = ENOSYS; return -1; }
    return real_setenv(name, value, overwrite);
}
int unsetenv(const char *name) {
    static int (*real_unsetenv)(const char *);
    if (!real_unsetenv) real_unsetenv = (void *)dlsym(RTLD_NEXT, "unsetenv");
    if (!in_hook) {
        in_hook++;
        for (struct env_hook *h = env_hooks; h; h = h->next) {
            if (h->value.hook_type != SUDO_HOOK_UNSETENV) continue;
            int rc = ((sudo_hook_fn_unsetenv_t)h->value.hook_fn)(name, h->value.closure);
            if (rc != SUDO_HOOK_RET_NEXT) { in_hook--; return rc == SUDO_HOOK_RET_STOP ? 0 : -1; }
        }
        in_hook--;
    }
    if (!real_unsetenv) { errno = ENOSYS; return -1; }
    return real_unsetenv(name);
}
int putenv(char *value) {
    static int (*real_putenv)(char *);
    if (!real_putenv) real_putenv = (void *)dlsym(RTLD_NEXT, "putenv");
    if (!in_hook) {
        in_hook++;
        for (struct env_hook *h = env_hooks; h; h = h->next) {
            if (h->value.hook_type != SUDO_HOOK_PUTENV) continue;
            int rc = ((sudo_hook_fn_putenv_t)h->value.hook_fn)(value, h->value.closure);
            if (rc != SUDO_HOOK_RET_NEXT) { in_hook--; return rc == SUDO_HOOK_RET_STOP ? 0 : -1; }
        }
        in_hook--;
    }
    if (!real_putenv) { errno = ENOSYS; return -1; }
    return real_putenv(value);
}

/* Event objects stay allocated until the end of the current dispatch. A
 * callback may delete/free itself or another event without invalidating traversal. */
struct event {
    struct sudo_plugin_event public;
    struct event *next;
    int fd, flags, ready;
    bool active, dead;
    int64_t deadline;
    sudo_plugin_ev_callback_t callback;
    void *closure;
};
static struct event *events;
static bool event_dispatching, event_break;
static struct pollfd *event_poll;
static size_t event_poll_capacity;
/* Like core.c's prompt wakeup pipe, this descriptor pair has process lifetime:
 * a signal can run on another runtime thread while a plugin is being removed. */
static int event_signal_pipe[2] = {-1, -1};
_Static_assert(ATOMIC_INT_LOCK_FREE == 2, "signal flags must be lock-free");
static atomic_uint event_signal_pending[NSIG], event_signal_wanted[NSIG];
static struct sigaction event_signal_saved[NSIG];
static bool event_signal_saved_valid[NSIG];
static void event_signal_handler(int signo, siginfo_t *info, void *context);
static int event_del(struct sudo_plugin_event *pub);

void ls_plugins_signal(int signo) {
    if (signo <= 0 || signo >= NSIG || !event_signal_wanted[signo]) return;
    int saved_errno = errno;
    event_signal_pending[signo] = 1;
    const char byte = 0;
    while (write(event_signal_pipe[1], &byte, 1) < 0 && errno == EINTR) {}
    errno = saved_errno;
}
static void event_signal_handler(int signo, siginfo_t *info, void *context) {
    int saved_errno = errno;
    ls_plugins_signal(signo);
    struct sigaction *old = &event_signal_saved[signo];
    if (old->sa_handler != SIG_DFL && old->sa_handler != SIG_IGN) {
        if (old->sa_flags & SA_SIGINFO) old->sa_sigaction(signo, info, context);
        else old->sa_handler(signo);
    } else if (!event_signal_wanted[signo] && old->sa_handler == SIG_DFL) {
        sigaction(signo, old, NULL);
        raise(signo);
    }
    errno = saved_errno;
}
static int event_signal_acquire(int signo) {
    if (event_signal_pipe[0] < 0 &&
        pipe2(event_signal_pipe, O_CLOEXEC | O_NONBLOCK) != 0) return -1;
    if (!event_signal_wanted[signo]) {
        struct sigaction action, old;
        memset(&action, 0, sizeof action);
        action.sa_sigaction = event_signal_handler;
        action.sa_flags = SA_SIGINFO | SA_RESTART;
        sigemptyset(&action.sa_mask);
        if (sigaction(signo, NULL, &old)) return -1;
        /* exec temporarily replaces our handler and may restore it after an
         * event was deleted; retain the original disposition in that case. */
        if (!(old.sa_flags & SA_SIGINFO) || old.sa_sigaction != event_signal_handler) {
            event_signal_saved[signo] = old;
            event_signal_saved_valid[signo] = true;
        }
        event_signal_wanted[signo] = 1;
        if (sigaction(signo, &action, NULL)) {
            event_signal_wanted[signo] = 0;
            return -1;
        }
        return 0;
    }
    event_signal_wanted[signo]++;
    return 0;
}
static void event_signal_restore(int signo) {
    struct sigaction current;
    if (event_signal_saved_valid[signo] && !sigaction(signo, NULL, &current) &&
        (current.sa_flags & SA_SIGINFO) && current.sa_sigaction == event_signal_handler)
        sigaction(signo, &event_signal_saved[signo], NULL);
}
static int64_t event_now(void) {
    struct timespec t;
    clock_gettime(CLOCK_MONOTONIC, &t);
    return (int64_t)t.tv_sec * 1000000000 + t.tv_nsec;
}
static int event_set(struct sudo_plugin_event *pub, int fd, int flags,
    sudo_plugin_ev_callback_t cb, void *closure) {
    struct event *e = (void *)pub;
    if (!cb || (flags & ~(SUDO_PLUGIN_EV_READ | SUDO_PLUGIN_EV_WRITE |
        SUDO_PLUGIN_EV_PERSIST | SUDO_PLUGIN_EV_TIMEOUT | SUDO_PLUGIN_EV_SIGNAL)) ||
        ((flags & SUDO_PLUGIN_EV_SIGNAL) && (fd <= 0 || fd >= NSIG ||
        fd == SIGKILL || fd == SIGSTOP || (flags & (SUDO_PLUGIN_EV_READ | SUDO_PLUGIN_EV_WRITE))))) {
        errno = EINVAL; return -1;
    }
    event_del(pub);
    e->fd = fd; e->flags = flags; e->callback = cb; e->closure = closure;
    e->active = false; e->deadline = 0;
    return 1;
}
static int event_add(struct sudo_plugin_event *pub, struct timespec *timeout) {
    struct event *e = (void *)pub;
    if (!e->callback || e->dead || (timeout &&
        (timeout->tv_sec < 0 || timeout->tv_nsec < 0 || timeout->tv_nsec >= 1000000000 ||
        timeout->tv_sec > (INT64_MAX - event_now()) / 1000000000))) {
        errno = EINVAL; return -1;
    }
    if (!e->active && (e->flags & SUDO_PLUGIN_EV_SIGNAL) && event_signal_acquire(e->fd)) return -1;
    e->deadline = timeout ? event_now() + (int64_t)timeout->tv_sec * 1000000000 + timeout->tv_nsec : 0;
    e->active = true; e->ready = 0;
    return 1;
}
static int event_del(struct sudo_plugin_event *pub) {
    struct event *e = (void *)pub;
    if (e->active && (e->flags & SUDO_PLUGIN_EV_SIGNAL)) {
        if (--event_signal_wanted[e->fd] == 0) event_signal_restore(e->fd);
    }
    e->active = false; e->ready = 0; return 1;
}
static int event_pending(struct sudo_plugin_event *pub, int flags, struct timespec *t) {
    struct event *e = (void *)pub;
    if (!e->active || e->dead) return 0;
    int result = e->flags & flags;
    if (e->deadline && (flags & SUDO_PLUGIN_EV_TIMEOUT)) {
        result |= SUDO_PLUGIN_EV_TIMEOUT;
        int64_t left = e->deadline - event_now();
        if (left < 0) left = 0;
        if (t) { t->tv_sec = left / 1000000000; t->tv_nsec = left % 1000000000; }
    }
    return result;
}
static int event_fd(struct sudo_plugin_event *pub) { return ((struct event *)pub)->fd; }
static void event_setbase(struct sudo_plugin_event *pub, void *base) {
    /* Only this host's default loop is a valid base in this ABI transport. */
    if (base != NULL) { errno = EINVAL; return; }
    event_del(pub);
}
static void event_loopbreak(struct sudo_plugin_event *pub) { (void)pub; event_break = true; }
static void event_collect(void) {
    for (struct event **p = &events; *p;) {
        if ((*p)->dead) { struct event *old = *p; *p = old->next; free(old); }
        else p = &(*p)->next;
    }
}
static void event_free(struct sudo_plugin_event *pub) {
    struct event *e = (void *)pub;
    event_del(pub);
    e->dead = true;
    if (!event_dispatching) event_collect();
}
static struct sudo_plugin_event *event_alloc(void) {
    struct event *e = calloc(1, sizeof(*e));
    if (!e) return NULL;
    e->public = (struct sudo_plugin_event){event_set, event_add, event_del,
        event_pending, event_fd, event_setbase, event_loopbreak, event_free};
    e->fd = -1; e->next = events; events = e;
    return &e->public;
}
static void events_free(void) {
    while (events) {
        struct event *e = events;
        event_del(&e->public);
        events = e->next; free(e);
    }
    for (int signo = 1; signo < NSIG; signo++) {
        event_signal_restore(signo);
        event_signal_pending[signo] = 0;
    }
    free(event_poll); event_poll = NULL; event_poll_capacity = 0; event_break = false;
}
int ls_plugins_poll(struct pollfd *fds, nfds_t count, int timeout) {
    size_t n = count;
    bool bridge = bridge_server >= 0 && bridge_owner == getpid();
    if (bridge) n++;
    for (struct event *e = events; e; e = e->next) if (e->active) n++;
    if (event_break) { errno = ECANCELED; return -1; }
    if (n == count) return poll(fds, count, timeout);
    bool signal_pipe = event_signal_pipe[0] >= 0;
    if (signal_pipe) n++;
    if (n > event_poll_capacity) {
        struct pollfd *p = realloc(event_poll, n * sizeof(*p));
        if (!p) return -1;
        event_poll = p; event_poll_capacity = n;
    }
    if (count) memcpy(event_poll, fds, count * sizeof(*fds));
    size_t i = count;
    if (signal_pipe) event_poll[i++] = (struct pollfd){event_signal_pipe[0], POLLIN, 0};
    if (bridge) event_poll[i++] = (struct pollfd){bridge_server, POLLIN, 0};
    int64_t now = event_now();
    for (struct event *e = events; e; e = e->next) {
        e->ready = 0;
        if (!e->active) continue;
        event_poll[i++] = (struct pollfd){(e->flags & SUDO_PLUGIN_EV_SIGNAL) ? -1 : e->fd,
            ((e->flags & SUDO_PLUGIN_EV_READ) ? POLLIN : 0) |
            ((e->flags & SUDO_PLUGIN_EV_WRITE) ? POLLOUT : 0), 0};
        if ((e->flags & SUDO_PLUGIN_EV_SIGNAL) && event_signal_pending[e->fd]) timeout = 0;
        if (e->deadline) {
            int64_t left = (e->deadline - now + 999999) / 1000000;
            int ms = left <= 0 ? 0 : left > INT_MAX ? INT_MAX : (int)left;
            if (timeout < 0 || ms < timeout) timeout = ms;
        }
    }
    int rc = poll(event_poll, n, timeout);
    if (rc < 0) return rc;
    if (count) memcpy(fds, event_poll, count * sizeof(*fds));
    if (signal_pipe) {
        char bytes[128];
        while (read(event_signal_pipe[0], bytes, sizeof bytes) > 0) {}
    }
    bool bridge_ready = bridge && event_poll[count + (signal_pipe ? 1 : 0)].revents;
    now = event_now(); i = count + (signal_pipe ? 1 : 0) + (bridge ? 1 : 0);
    unsigned signal_ready[NSIG] = {0};
    for (int signo = 1; signo < NSIG; signo++)
        signal_ready[signo] = atomic_exchange(&event_signal_pending[signo], 0);
    event_dispatching = true;
    /* Capture readiness before callbacks can alter the active set. */
    for (struct event *e = events; e; e = e->next) {
        if (!e->active) continue;
        short ready = event_poll[i++].revents;
        int what = 0;
        if (ready & (POLLIN | POLLHUP | POLLERR | POLLNVAL)) what |= e->flags & SUDO_PLUGIN_EV_READ;
        if (ready & (POLLOUT | POLLHUP | POLLERR | POLLNVAL)) what |= e->flags & SUDO_PLUGIN_EV_WRITE;
        if (e->deadline && now >= e->deadline) what |= SUDO_PLUGIN_EV_TIMEOUT;
        if ((e->flags & SUDO_PLUGIN_EV_SIGNAL) && signal_ready[e->fd]) what |= SUDO_PLUGIN_EV_SIGNAL;
        e->ready = what;
    }
    for (struct event *e = events, *next; e; e = next) {
        next = e->next;
        if (!e->active) continue;
        int what = e->ready;
        if (!what || e->dead) continue;
        if (!(e->flags & SUDO_PLUGIN_EV_PERSIST)) event_del(&e->public);
        if (what & SUDO_PLUGIN_EV_TIMEOUT) e->deadline = 0;
        e->callback(e->fd, what, e->closure);
        if (event_break) break;
    }
    event_dispatching = false; event_collect();
    if (event_break) { errno = ECANCELED; return -1; }
    if (bridge_ready && bridge_dispatch()) return -1;
    int ready = 0;
    for (nfds_t j = 0; j < count; j++) if (fds[j].revents) ready++;
    return ready;
}

LEAN_EXPORT lean_obj_res lean_sudo_plugins_conversation(uint8_t use_stdin,
    uint8_t noninteractive, uint8_t bell, b_lean_obj_arg askpass) {
    if (ls_plugin_conversation_config(bell, lean_string_cstr(askpass)) != 0)
        return error("unable to configure plugin conversation");
    conv_stdin = use_stdin; conv_noninteractive = noninteractive;
    return ok();
}

static bool fact(lean_object **array, const char *fmt, ...) {
    char stack[512], *value = stack;
    va_list ap, copy;
    va_start(ap, fmt); va_copy(copy, ap);
    int n = vsnprintf(stack, sizeof stack, fmt, ap);
    va_end(ap);
    if (n < 0) { va_end(copy); return false; }
    if ((size_t)n >= sizeof stack) {
        value = malloc((size_t)n + 1);
        if (!value) { va_end(copy); return false; }
        vsnprintf(value, (size_t)n + 1, fmt, copy);
    }
    va_end(copy);
    if (!ls_plugin_utf8_valid(value, (size_t)n)) {
        if (value != stack) free(value);
        errno = EILSEQ;
        return false;
    }
    *array = lean_array_push(*array, lean_mk_string(value));
    if (value != stack) free(value);
    return true;
}
static unsigned dimension(const char *name, unsigned fallback) {
    const char *s = getenv(name);
    if (!s || !*s) return fallback;
    unsigned n = 0;
    for (; *s; s++) {
        if (*s < '0' || *s > '9' || n > ((unsigned)INT_MAX - (unsigned)(*s - '0')) / 10)
            return fallback;
        n = n * 10 + (unsigned)(*s - '0');
    }
    return n ? n : fallback;
}
LEAN_EXPORT lean_obj_res lean_sudo_plugins_user_info(b_lean_obj_arg group_source, uint32_t max_groups) {
    lean_object *a = lean_mk_empty_array_with_capacity(lean_box(40));
    struct passwd *pw = getpwuid(getuid());
    if (!pw) { lean_dec(a); return error("you do not exist in the passwd database"); }
    int tty = open("/dev/tty", O_RDWR | O_NOCTTY | O_CLOEXEC);
    pid_t tcpgid = tty < 0 ? 0 : tcgetpgrp(tty), sid = getsid(0);
    if (tcpgid < 0) tcpgid = 0;
    if (sid < 0) sid = 0;
    struct winsize ws = {0};
    if (tty >= 0) ioctl(tty, TIOCGWINSZ, &ws);
    unsigned rows = ws.ws_row && ws.ws_col ? ws.ws_row : dimension("LINES", 24);
    unsigned cols = ws.ws_row && ws.ws_col ? ws.ws_col : dimension("COLUMNS", 80);
    if (!fact(&a, "user=%s", pw->pw_name) ||
        !fact(&a, "pid=%ld", (long)getpid()) || !fact(&a, "ppid=%ld", (long)getppid()) ||
        !fact(&a, "pgid=%ld", (long)getpgrp()) || !fact(&a, "tcpgid=%ld", (long)tcpgid) ||
        !fact(&a, "sid=%ld", (long)sid) ||
        !fact(&a, "uid=%u", (unsigned)getuid()) || !fact(&a, "euid=%u", (unsigned)geteuid()) ||
        !fact(&a, "gid=%u", (unsigned)getgid()) || !fact(&a, "egid=%u", (unsigned)getegid())) goto oom;
    const char *source = lean_string_cstr(group_source);
    long kernel_max = sysconf(_SC_NGROUPS_MAX);
    if (kernel_max < 0) kernel_max = NGROUPS_MAX;
    int ngroups = strcmp(source, "dynamic") ? getgroups(0, NULL) : 0;
    gid_t *groups = NULL;
    if (ngroups > 0 && (ngroups != kernel_max || !strcmp(source, "static"))) {
        groups = malloc((size_t)ngroups * sizeof(*groups));
        if (!groups) goto oom;
        ngroups = getgroups(ngroups, groups);
        if (ngroups < 0) { free(groups); groups = NULL; }
    }
    if (!groups) {
        const char *user = lean_string_cstr(lean_array_get_core(a, 0)) + sizeof("user=") - 1;
        int needed = 0;
        getgrouplist(user, getgid(), NULL, &needed);
        if (needed <= 0 || max_groups > INT_MAX) goto failed;
        int capacity = max_groups && (uint32_t)needed > max_groups ? (int)max_groups : needed;
        groups = malloc((size_t)capacity * sizeof(*groups));
        if (!groups) goto oom;
        ngroups = capacity;
        int rc = getgrouplist(user, getgid(), groups, &ngroups);
        if (rc < 0) {
            if (max_groups && capacity == (int)max_groups) ngroups = capacity;
            else { free(groups); goto failed; }
        }
    }
    /* Ten decimal digits per gid, a comma, and the terminating NUL. */
    size_t cap = 8 + (size_t)ngroups * 11;
    char *group_text = malloc(cap);
    if (!group_text) { free(groups); goto oom; }
    size_t used = (size_t)snprintf(group_text, cap, "groups=");
    for (int i = 0; i < ngroups; i++)
        used += (size_t)snprintf(group_text + used, cap - used, "%s%u", i ? "," : "", (unsigned)groups[i]);
    free(groups);
    a = lean_array_push(a, lean_mk_string(group_text)); free(group_text);
    mode_t mask = umask(0); umask(mask);
    if (!fact(&a, "umask=0%o", (unsigned)mask)) goto oom;
    char *cwd = getcwd(NULL, 0);
    if (cwd) {
        bool rc = fact(&a, "cwd=%s", cwd);
        free(cwd); if (!rc) goto oom;
    }
    /* /dev/tty denotes the controlling terminal but its stat device is 5:0.
     * TIOCGDEV reports the actual terminal device even with redirected stdio. */
    unsigned dev = 0;
    char name[PATH_MAX] = {0};
    bool have_dev = false;
#ifdef TIOCGDEV
    if (tty >= 0 && ioctl(tty, TIOCGDEV, &dev) == 0) have_dev = true;
#endif
    for (int fd = 0; fd < 3; fd++) {
        if (ttyname_r(fd, name, sizeof name) == 0) {
            struct stat st;
            if (fstat(fd, &st) == 0 && (!have_dev || st.st_rdev == (dev_t)dev)) {
                dev = (unsigned)st.st_rdev; have_dev = true; break;
            }
        }
        name[0] = 0;
    }
#ifdef __linux__
    if (have_dev && !name[0]) {
        /* Linux devpts encodes the pts index in the device minor number. */
        unsigned maj = (dev >> 8) & 0xfff;
        unsigned min = (dev & 0xff) | ((dev >> 12) & 0xfff00);
        if (maj >= 136 && maj <= 143)
            snprintf(name, sizeof name, "/dev/pts/%u", (maj - 136) * 256 + min);
        else if (maj == 4)
            snprintf(name, sizeof name, min < 64 ? "/dev/tty%u" : "/dev/ttyS%u",
                min < 64 ? min : min - 64);
        if (name[0]) {
            struct stat st;
            if (stat(name, &st) || st.st_rdev != (dev_t)dev) name[0] = 0;
        }
    }
#endif
    if (have_dev && !fact(&a, "ttydev=%llu", (unsigned long long)dev)) goto oom;
    if (name[0] && !fact(&a, "tty=%s", name)) goto oom;
    char host[HOST_NAME_MAX + 1];
    if (gethostname(host, sizeof host) != 0) strcpy(host, "localhost");
    host[sizeof host - 1] = 0;
    if (!fact(&a, "host=%s", host) || !fact(&a, "lines=%u", rows) || !fact(&a, "cols=%u", cols)) goto oom;
    static const struct { int resource; const char *name; } limits[] = {
        {RLIMIT_AS, "as"}, {RLIMIT_CORE, "core"}, {RLIMIT_CPU, "cpu"},
        {RLIMIT_DATA, "data"}, {RLIMIT_FSIZE, "fsize"}, {RLIMIT_LOCKS, "locks"},
        {RLIMIT_MEMLOCK, "memlock"},
        {RLIMIT_NOFILE, "nofile"}, {RLIMIT_NPROC, "nproc"}, {RLIMIT_RSS, "rss"},
        {RLIMIT_STACK, "stack"}
    };
    for (size_t i = 0; i < sizeof limits / sizeof limits[0]; i++) {
        struct rlimit lim;
        if (getrlimit(limits[i].resource, &lim)) continue;
        char soft[32], hard[32];
        if (lim.rlim_cur == RLIM_INFINITY) strcpy(soft, "infinity");
        else snprintf(soft, sizeof soft, "%llu", (unsigned long long)lim.rlim_cur);
        if (lim.rlim_max == RLIM_INFINITY) strcpy(hard, "infinity");
        else snprintf(hard, sizeof hard, "%llu", (unsigned long long)lim.rlim_max);
        if (!fact(&a, "rlimit_%s=%s,%s", limits[i].name, soft, hard)) goto oom;
    }
    if (tty >= 0) close(tty);
    return lean_io_result_mk_ok(a);
oom:
    errno = ENOMEM;
failed:
    if (tty >= 0) close(tty);
    lean_dec(a); return error("unable to collect plugin user information");
}
