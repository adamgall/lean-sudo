#ifndef SUDO_PLUGIN_H
#define SUDO_PLUGIN_H

#define SUDO_API_VERSION_MAJOR 1
#define SUDO_API_VERSION_MINOR 22
#define SUDO_API_MKVERSION(x, y) (((x) << 16) | (y))
#define SUDO_API_VERSION SUDO_API_MKVERSION(SUDO_API_VERSION_MAJOR, SUDO_API_VERSION_MINOR)

#define SUDO_API_VERSION_GET_MAJOR(v) ((v) >> 16)
#define SUDO_API_VERSION_GET_MINOR(v) ((v) & 0xffffU)

#define SUDO_FRONT_END		0

struct sudo_conv_message {
#define SUDO_CONV_PROMPT_ECHO_OFF   0x0001
#define SUDO_CONV_PROMPT_ECHO_ON    0x0002
#define SUDO_CONV_ERROR_MSG	    0x0003
#define SUDO_CONV_INFO_MSG	    0x0004
#define SUDO_CONV_PROMPT_MASK	    0x0005
#define SUDO_CONV_PROMPT_ECHO_OK    0x1000
#define SUDO_CONV_PREFER_TTY	    0x2000
    int msg_type;
    int timeout;
    const char *msg;
};

#define SUDO_CONV_REPL_MAX	1023

struct sudo_conv_reply {
    char *reply;
};

typedef int (*sudo_conv_callback_fn_t)(int signo, void *closure);
struct sudo_conv_callback {
    unsigned int version;
    void *closure;
    sudo_conv_callback_fn_t on_suspend;
    sudo_conv_callback_fn_t on_resume;
};

typedef int (*sudo_conv_t)(int num_msgs, const struct sudo_conv_message msgs[],
	struct sudo_conv_reply replies[], struct sudo_conv_callback *callback);
typedef int (*sudo_printf_t)(int msg_type, const char * restrict fmt, ...);

#if defined(__GNUC__) && ((__GNUC__ == 4 && __GNUC_MINOR__ >= 4) || __GNUC__ > 4)
# pragma GCC diagnostic ignored "-Wstrict-prototypes"
#endif

#if defined(__STDC_VERSION__) && (__STDC_VERSION__ >= 202311L)
typedef int (*sudo_hook_fn_t)(...);
#else
typedef int (*sudo_hook_fn_t)();
#endif
typedef int (*sudo_hook_fn_setenv_t)(const char *name, const char *value, int overwrite, void *closure);
typedef int (*sudo_hook_fn_putenv_t)(char *string, void *closure);
typedef int (*sudo_hook_fn_getenv_t)(const char *name, char **value, void *closure);
typedef int (*sudo_hook_fn_unsetenv_t)(const char *name, void *closure);

struct sudo_hook {
    unsigned int hook_version;
    unsigned int hook_type;
    sudo_hook_fn_t hook_fn;
    void *closure;
};

#define SUDO_HOOK_VERSION_MAJOR	1
#define SUDO_HOOK_VERSION_MINOR	0
#define SUDO_HOOK_VERSION SUDO_API_MKVERSION(SUDO_HOOK_VERSION_MAJOR, SUDO_HOOK_VERSION_MINOR)

#define SUDO_HOOK_RET_ERROR	-1
#define SUDO_HOOK_RET_NEXT	0
#define SUDO_HOOK_RET_STOP	1

#define SUDO_HOOK_SETENV	1
#define SUDO_HOOK_UNSETENV	2
#define SUDO_HOOK_PUTENV	3
#define SUDO_HOOK_GETENV	4

typedef void (*sudo_plugin_ev_callback_t)(int fd, int what, void *closure);

struct timespec;
struct sudo_plugin_event {
    int (*set)(struct sudo_plugin_event *pev, int fd, int events, sudo_plugin_ev_callback_t callback, void *closure);
    int (*add)(struct sudo_plugin_event *pev, struct timespec *timeout);
    int (*del)(struct sudo_plugin_event *pev);
    int (*pending)(struct sudo_plugin_event *pev, int events, struct timespec *ts);
    int (*fd)(struct sudo_plugin_event *pev);
    void (*setbase)(struct sudo_plugin_event *pev, void *base);
    void (*loopbreak)(struct sudo_plugin_event *pev);
    void (*free)(struct sudo_plugin_event *pev);
};

#define SUDO_PLUGIN_EV_TIMEOUT	0x01
#define SUDO_PLUGIN_EV_READ	0x02
#define SUDO_PLUGIN_EV_WRITE	0x04
#define SUDO_PLUGIN_EV_PERSIST	0x08
#define SUDO_PLUGIN_EV_SIGNAL	0x10

#define SUDO_POLICY_PLUGIN     1

struct io_plugin {
#define SUDO_IO_PLUGIN	    2
    unsigned int type;
    unsigned int version;
    int (*open)(unsigned int version, sudo_conv_t conversation,
	sudo_printf_t sudo_plugin_printf, char * const settings[],
	char * const user_info[], char * const command_info[],
	int argc, char * const argv[], char * const user_env[],
	char * const plugin_options[], const char **errstr);
    void (*close)(int exit_status, int error);
    int (*show_version)(int verbose);
    int (*log_ttyin)(const char *buf, unsigned int len, const char **errstr);
    int (*log_ttyout)(const char *buf, unsigned int len, const char **errstr);
    int (*log_stdin)(const char *buf, unsigned int len, const char **errstr);
    int (*log_stdout)(const char *buf, unsigned int len, const char **errstr);
    int (*log_stderr)(const char *buf, unsigned int len, const char **errstr);
    void (*register_hooks)(int version,
	int (*register_hook)(struct sudo_hook *hook));
    void (*deregister_hooks)(int version,
	int (*deregister_hook)(struct sudo_hook *hook));
    int (*change_winsize)(unsigned int line, unsigned int cols,
	const char **errstr);
    int (*log_suspend)(int signo, const char **errstr);
    struct sudo_plugin_event * (*event_alloc)(void);
};

#define SUDO_PLUGIN_NO_STATUS		0
#define SUDO_PLUGIN_WAIT_STATUS		1
#define SUDO_PLUGIN_EXEC_ERROR		2
#define SUDO_PLUGIN_SUDO_ERROR		3

struct audit_plugin {
#define SUDO_AUDIT_PLUGIN	    3
    unsigned int type;
    unsigned int version;
    int (*open)(unsigned int version, sudo_conv_t conversation,
	sudo_printf_t sudo_plugin_printf, char * const settings[],
	char * const user_info[], int submit_optind,
	char * const submit_argv[], char * const submit_envp[],
	char * const plugin_options[], const char **errstr);
    void (*close)(int status_type, int status);
    int (*accept)(const char *plugin_name, unsigned int plugin_type,
	char * const command_info[], char * const run_argv[],
	char * const run_envp[], const char **errstr);
    int (*reject)(const char *plugin_name, unsigned int plugin_type,
	const char *audit_msg, char * const command_info[],
	const char **errstr);
    int (*error)(const char *plugin_name, unsigned int plugin_type,
	const char *audit_msg, char * const command_info[],
	const char **errstr);
    int (*show_version)(int verbose);
    void (*register_hooks)(int version, int (*register_hook)(struct sudo_hook *hook));
    void (*deregister_hooks)(int version, int (*deregister_hook)(struct sudo_hook *hook));
    struct sudo_plugin_event * (*event_alloc)(void);
};

struct approval_plugin {
#define SUDO_APPROVAL_PLUGIN	    4
    unsigned int type;
    unsigned int version;
    int (*open)(unsigned int version, sudo_conv_t conversation,
	sudo_printf_t sudo_plugin_printf, char * const settings[],
	char * const user_info[], int submit_optind,
	char * const submit_argv[], char * const submit_envp[],
	char * const plugin_options[], const char **errstr);
    void (*close)(void);
    int (*check)(char * const command_info[], char * const run_argv[],
	char * const run_envp[], const char **errstr);
    int (*show_version)(int verbose);
};

struct passwd;
struct sudoers_group_plugin {
    unsigned int version;
    int (*init)(int version, sudo_printf_t sudo_plugin_printf,
	char *const argv[]);
    void (*cleanup)(void);
    int (*query)(const char *user, const char *group, const struct passwd *pwd);
};

#endif
