/* sudo's stable group-provider ABI. Configuration/matching stays in Lean. */
#include "shim.h"
#include "sudo_plugin.h"
#include <dlfcn.h>
#include <errno.h>
#include <limits.h>
#include <pwd.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>

struct group_handle {
    void *dso;
    struct sudoers_group_plugin *plugin;
    char **args;
};

static void group_close(struct group_handle *h) {
    if (h->plugin != NULL) {
        h->plugin->cleanup();
        h->plugin = NULL;
    }
    if (h->dso != NULL) { dlclose(h->dso); h->dso = NULL; }
    ls_strv_free(h->args);
    h->args = NULL;
}
static void group_finalize(void *data) {
    struct group_handle *h = data;
    group_close(h);
    free(h);
}
static void group_foreach(void *data, b_lean_obj_arg fn) { (void)data; (void)fn; }
static lean_external_class *group_class;

static lean_obj_res group_error(struct group_handle *h, const char *fmt, ...) {
    va_list ap;
    va_start(ap, fmt);
    char *message = NULL;
    int rc = vasprintf(&message, fmt, ap);
    va_end(ap);
    lean_object *error = lean_mk_io_user_error(lean_mk_string(
        rc < 0 ? "unable to allocate memory" : message));
    free(message);
    group_finalize(h);
    return lean_io_result_mk_error(error);
}

static int group_printf(int type, const char *fmt, ...) {
    va_list ap;
    va_start(ap, fmt);
    int rc = vfprintf((type & 0xff) == 4 ? stdout : stderr, fmt, ap);
    va_end(ap);
    return rc;
}

/* Match sudo's LP64 Linux retry for /lib/foo.so -> /lib64/foo.so. */
static int group_fallback(char path[PATH_MAX]) {
    char alternate[PATH_MAX];
    const char *slash = strrchr(path, '/');
    if (slash == NULL) return 0;
    const char *base = slash + 1;
    while (slash > path && slash[-1] == '/') --slash;
    size_t n = (size_t)(slash - path);
    if (n < 4 || memcmp(slash - 4, "/lib", 4) != 0) return 0;
    int len = snprintf(alternate, sizeof alternate, "%.*s/lib64/%s", (int)(n - 4), path, base);
    struct stat st;
    if (len < 0 || (size_t)len >= sizeof alternate || stat(alternate, &st) != 0) return 0;
    memcpy(path, alternate, (size_t)len + 1);
    return 1;
}

LEAN_EXPORT lean_obj_res lean_sudo_group_plugin_load(b_lean_obj_arg path_obj,
        b_lean_obj_arg args, lean_obj_arg world) {
    (void)world;
    struct group_handle *h = calloc(1, sizeof(*h));
    if (h == NULL) return ls_error("unable to allocate memory");
    const char *name = lean_string_cstr(path_obj);
    char path[PATH_MAX];
    size_t len = strlen(name);
    if (len >= sizeof path) return group_error(h, "%s: %s", name, strerror(ENAMETOOLONG));
    memcpy(path, name, len + 1);
    h->dso = dlopen(path, RTLD_LAZY | RTLD_GLOBAL);
    if (h->dso == NULL && group_fallback(path)) h->dso = dlopen(path, RTLD_LAZY | RTLD_GLOBAL);
    if (h->dso == NULL) {
        const char *error = dlerror();
        return group_error(h, "unable to load %s: %s", path, error ? error : "unknown error");
    }
    struct sudoers_group_plugin *plugin = dlsym(h->dso, "group_plugin");
    if (plugin == NULL) return group_error(h, "unable to find symbol \"group_plugin\" in %s", path);
    if ((plugin->version >> 16) != 1) return group_error(h,
        "%s: incompatible group plugin major version %u, expected 1", path, plugin->version >> 16);
    if (plugin->init == NULL || plugin->query == NULL || plugin->cleanup == NULL)
        return group_error(h, "%s: incomplete group plugin interface", path);
    size_t count = lean_array_size(args);
    if (count != 0) {
        h->args = calloc(count + 1, sizeof(*h->args));
        if (h->args == NULL) return group_error(h, "unable to allocate memory");
        for (size_t i = 0; i < count; ++i) {
            h->args[i] = strdup(lean_string_cstr(lean_array_get_core(args, i)));
            if (h->args[i] == NULL) return group_error(h, "unable to allocate memory");
        }
    }
    if (plugin->init(1 << 16, group_printf, h->args) != 1) {
        group_finalize(h);
        return lean_io_result_mk_ok(lean_box(0));
    }
    h->plugin = plugin;
    if (group_class == NULL) group_class = lean_register_external_class(group_finalize, group_foreach);
    lean_object *some = lean_alloc_ctor(1, 1, 0);
    lean_ctor_set(some, 0, lean_alloc_external(group_class, h));
    return lean_io_result_mk_ok(some);
}

LEAN_EXPORT lean_obj_res lean_sudo_group_plugin_query(b_lean_obj_arg handle,
        b_lean_obj_arg user, b_lean_obj_arg group, lean_obj_arg world) {
    (void)world;
    struct group_handle *h = lean_get_external_data(handle);
    if (h->plugin == NULL) return lean_io_result_mk_ok(lean_box(0));
    const char *name = lean_string_cstr(user);
    struct passwd *pw = getpwnam(name);
    int result = h->plugin->query(name, lean_string_cstr(group), pw);
    return lean_io_result_mk_ok(lean_box(result == 1));
}

LEAN_EXPORT lean_obj_res lean_sudo_group_plugin_close(b_lean_obj_arg handle, lean_obj_arg world) {
    (void)world;
    group_close(lean_get_external_data(handle));
    return lean_io_result_mk_ok(lean_box(0));
}
