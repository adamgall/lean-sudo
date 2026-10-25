/* Integration-only sudo 1.9.17p2 / API 1.22 plugins.  Built against the
 * upstream header, independently of lean-sudo's ABI declarations. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sudo_plugin.h>

struct fixture {
    FILE *log;
    sudo_printf_t print;
};
static struct fixture approval, io, audit;
static const char *deny, *fail_command;
static int io_hook_version;
static unsigned audit_accepts;
static const char *audit_fail_command, *audit_fail_name;

static const char *value(char *const entries[], const char *key)
{
    size_t len = strlen(key);
    if (entries != NULL)
        for (; *entries != NULL; entries++)
            if (strncmp(*entries, key, len) == 0 && (*entries)[len] == '=')
                return *entries + len + 1;
    return NULL;
}

static void vector(FILE *fp, const char *name, char *const entries[])
{
    if (entries != NULL)
        for (; *entries != NULL; entries++)
            fprintf(fp, "%s=%s\n", name, *entries);
}

static int open_fixture(struct fixture *f, const char *name, unsigned int version,
    sudo_printf_t print, char *const settings[], char *const user_info[],
    char *const options[], const char **errstr)
{
    const char *path = value(options, "log");
    f->print = print;
    if (path == NULL || (f->log = fopen(path, "a")) == NULL) {
        *errstr = "fixture log unavailable";
        return -1;
    }
    setvbuf(f->log, NULL, _IONBF, 0);
    fprintf(f->log, "%s.open\napi=%u\n", name, version);
    vector(f->log, "option", options);
    vector(f->log, "setting", settings);
    vector(f->log, "user", user_info);
    return 1;
}

static int approval_open(unsigned int version, sudo_conv_t conversation,
    sudo_printf_t print, char *const settings[], char *const user_info[],
    int optind, char *const argv[], char *const envp[], char *const options[],
    const char **errstr)
{
    (void)conversation;
    if (open_fixture(&approval, "approval", version, print, settings,
            user_info, options, errstr) != 1)
        return -1;
    fprintf(approval.log, "submit_optind=%d\n", optind);
    vector(approval.log, "submit", argv);
    vector(approval.log, "submit_env", envp);
    deny = value(options, "deny");
    fail_command = value(options, "error");
    return 1;
}

static int approval_check(char *const info[], char *const argv[],
    char *const envp[], const char **errstr)
{
    const char *command = value(info, "command");
    const char *base = command == NULL ? NULL : strrchr(command, '/');
    if (base != NULL) base++;
    else base = command;
    fputs("approval.check\n", approval.log);
    vector(approval.log, "command_info", info);
    vector(approval.log, "run", argv);
    vector(approval.log, "run_env", envp);
    if (fail_command != NULL && base != NULL && strcmp(fail_command, base) == 0) {
        *errstr = "sample approval check failed";
        approval.print(SUDO_CONV_ERROR_MSG, "%s\n", *errstr);
        return -1;
    }
    if (deny != NULL && base != NULL && strcmp(deny, base) == 0) {
        *errstr = "sample approval denied command name";
        approval.print(SUDO_CONV_ERROR_MSG, "%s\n", *errstr);
        return 0;
    }
    return 1;
}

static void approval_close(void)
{
    fputs("approval.close\n", approval.log);
    fclose(approval.log);
    approval.log = NULL;
}

static int approval_version(int verbose)
{
    approval.print(SUDO_CONV_INFO_MSG, "fixture approval version 1.22 verbose=%d\n", verbose);
    return 1;
}

struct approval_plugin sample_approval = {
    .type = SUDO_APPROVAL_PLUGIN, .version = SUDO_API_VERSION,
    .open = approval_open, .close = approval_close,
    .check = approval_check, .show_version = approval_version
};

static int io_open(unsigned int version, sudo_conv_t conversation,
    sudo_printf_t print, char *const settings[], char *const user_info[],
    char *const info[], int argc, char *const argv[], char *const envp[],
    char *const options[], const char **errstr)
{
    const char *mode;
    (void)conversation;
    if (open_fixture(&io, "io", version, print, settings, user_info,
            options, errstr) != 1)
        return -1;
    fprintf(io.log, "argc=%d\nio.hooks.version=%d\n", argc, io_hook_version);
    vector(io.log, "command_info", info);
    vector(io.log, "run", argv);
    vector(io.log, "run_env", envp);
    mode = value(options, "open");
    if (mode != NULL && strcmp(mode, "disable") == 0) {
        fputs("io.disabled\n", io.log);
        fclose(io.log);
        io.log = NULL;
        return 0;
    }
    if (mode != NULL && strcmp(mode, "error") == 0) {
        *errstr = "fixture IO open failed";
        fclose(io.log);
        io.log = NULL;
        return -1;
    }
    return 1;
}

static void io_close(int status, int error)
{
    fprintf(io.log, "io.close status=%d error=%d\n", status, error);
    fclose(io.log);
    io.log = NULL;
}

static int io_version(int verbose)
{
    io.print(SUDO_CONV_INFO_MSG, "fixture IO version 1.22 verbose=%d\n", verbose);
    return 1;
}

/* Hex encoding preserves binary bytes and lets tests join arbitrary callback
 * chunk boundaries without imposing a scheduler-dependent chunk count. */
static int io_bytes(const char *name, const char *buf, unsigned int len)
{
    unsigned int i;
    fprintf(io.log, "io.%s=", name);
    for (i = 0; i < len; i++) fprintf(io.log, "%02x", (unsigned char)buf[i]);
    fputc('\n', io.log);
    return 1;
}
#define STREAM(name) \
    static int io_##name(const char *buf, unsigned int len, const char **errstr) \
    { (void)errstr; return io_bytes(#name, buf, len); }
STREAM(ttyin)
STREAM(ttyout)
STREAM(stdin)
STREAM(stdout)
STREAM(stderr)

static void io_register_hooks(int version, int (*register_hook)(struct sudo_hook *))
{
    (void)register_hook;
    io_hook_version = version;
}

struct io_plugin sample_io = {
    .type = SUDO_IO_PLUGIN, .version = SUDO_API_VERSION,
    .open = io_open, .close = io_close, .show_version = io_version,
    .log_ttyin = io_ttyin, .log_ttyout = io_ttyout,
    .log_stdin = io_stdin, .log_stdout = io_stdout, .log_stderr = io_stderr,
    .register_hooks = io_register_hooks
};

static int audit_open(unsigned int version, sudo_conv_t conversation,
    sudo_printf_t print, char *const settings[], char *const user_info[],
    int optind, char *const argv[], char *const envp[], char *const options[],
    const char **errstr)
{
    (void)conversation;
    audit_accepts = 0;
    audit_fail_command = value(options, "fail_command");
    audit_fail_name = value(options, "fail_name");
    if (open_fixture(&audit, "audit", version, print, settings, user_info,
            options, errstr) != 1)
        return -1;
    fprintf(audit.log, "submit_optind=%d\n", optind);
    vector(audit.log, "submit", argv);
    vector(audit.log, "submit_env", envp);
    return 1;
}

static int audit_accept(const char *name, unsigned int type, char *const info[],
    char *const argv[], char *const envp[], const char **errstr)
{
    audit_accepts++;
    vector(audit.log, "audit.command_info", info);
    vector(audit.log, "audit.run", argv);
    vector(audit.log, "audit.run_env", envp);
    fprintf(audit.log, "audit.accept name=%s type=%u\n", name, type);
    const char *command = value(info, "command");
    if (audit_fail_command != NULL && command != NULL &&
        strcmp(audit_fail_command, command) == 0 &&
        (audit_fail_name == NULL || strcmp(audit_fail_name, name) == 0)) {
        *errstr = "sample audit accept failed";
        return -1;
    }
    return 1;
}

static int audit_reject(const char *name, unsigned int type, const char *message,
    char *const info[], const char **errstr)
{
    (void)info; (void)errstr;
    fprintf(audit.log, "audit.reject name=%s type=%u reason=%s\n", name, type, message);
    return 1;
}

static int audit_error(const char *name, unsigned int type, const char *message,
    char *const info[], const char **errstr)
{
    (void)info; (void)errstr;
    fprintf(audit.log, "audit.error name=%s type=%u reason=%s\n", name, type, message);
    return 1;
}

static void audit_close(int type, int status)
{
    fprintf(audit.log, "audit.close type=%d status=%d\n", type, status);
    fprintf(audit.log, "audit.accepts=%u\n", audit_accepts);
    fclose(audit.log);
    audit.log = NULL;
}

static int audit_version(int verbose)
{
    audit.print(SUDO_CONV_INFO_MSG, "fixture audit version 1.22 verbose=%d\n", verbose);
    return 1;
}

struct audit_plugin sample_audit = {
    .type = SUDO_AUDIT_PLUGIN, .version = SUDO_API_VERSION,
    .open = audit_open, .close = audit_close, .accept = audit_accept,
    .reject = audit_reject, .error = audit_error, .show_version = audit_version
};

struct approval_plugin bad_version = {
    .type = SUDO_APPROVAL_PLUGIN, .version = SUDO_API_MKVERSION(2, 0)
};
