/* SSSD sudo responder ABI boundary. All policy interpretation lives in Lean. */
#include "shim.h"
#include <dlfcn.h>
#include <errno.h>
#include <limits.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/types.h>

/* Stable interface from sudo 1.9.17p2 plugins/sudoers/sssd.c. */
struct sss_sudo_attr {
  char *name;
  char **values;
  unsigned int num_values;
};
struct sss_sudo_rule {
  unsigned int num_attrs;
  struct sss_sudo_attr *attrs;
};
struct sss_sudo_result {
  unsigned int num_rules;
  struct sss_sudo_rule *rules;
};
struct sss_api {
  int (*send_recv)(uid_t, const char *, const char *, uint32_t *, struct sss_sudo_result **);
  int (*send_recv_defaults)(uid_t, const char *, uint32_t *, char **, struct sss_sudo_result **);
  void (*free_result)(struct sss_sudo_result *);
  int (*get_values)(struct sss_sudo_rule *, const char *, char ***);
  void (*free_values)(char **);
};

static lean_obj_res failure(const char *operation, int error) {
  char message[512];
  snprintf(message, sizeof message, "SSSD %s: %s", operation, strerror(error));
  return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(message)));
}


static void *open_library(void) {
  static const char *const paths[] = {
#if defined(__linux__) && defined(__x86_64__)
    "/usr/lib/x86_64-linux-gnu/libsss_sudo.so",
#elif defined(__linux__) && defined(__aarch64__)
    "/usr/lib/aarch64-linux-gnu/libsss_sudo.so",
#endif
    "/usr/lib64/libsss_sudo.so", "/usr/lib/libsss_sudo.so",
    "libsss_sudo.so", "libsss_sudo.so.0"
  };
  for (size_t i = 0; i < sizeof paths / sizeof paths[0]; i++) {
    void *handle = dlopen(paths[i], RTLD_NOW | RTLD_LOCAL);
    if (handle) return handle;
  }
  return NULL;
}

static bool load_api(void *handle, struct sss_api *api) {
  const struct ls_symbol symbols[] = {
    {"sss_sudo_send_recv", &api->send_recv},
    {"sss_sudo_send_recv_defaults", &api->send_recv_defaults},
    {"sss_sudo_free_result", &api->free_result},
    {"sss_sudo_get_values", &api->get_values},
    {"sss_sudo_free_values", &api->free_values}
  };
  return ls_dlsyms(handle, symbols, sizeof symbols / sizeof symbols[0]) == NULL;
}

/* A failed request may return an SSS status with errno in server_error,
 * or a positive errno directly. Do not mistake malformed replies for absence. */
static int request_error(int rc, uint32_t server_error, int saved_errno) {
  if (server_error > 0) return server_error <= INT_MAX ? (int)server_error : EIO;
  if (rc > 0) return rc;
  return saved_errno ? saved_errno : EIO;
}

static bool unavailable(int error) {
  return error == ENOENT || error == ECONNREFUSED || error == ECONNRESET ||
    error == ENOTCONN || error == ETIMEDOUT || error == EPIPE ||
    error == EHOSTUNREACH || error == ENETUNREACH || error == ENETDOWN ||
    error == EAGAIN;
}

/* Only publish a complete result. get_values owns its NULL-terminated copy;
 * free_values must run before free_result and dlclose on every path. */
static int copy_result(const struct sss_api *api, struct sss_sudo_result *result,
    lean_object **out) {
  if (!result || (result->num_rules && !result->rules)) return EPROTO;
  lean_object *rules = lean_mk_empty_array_with_capacity(lean_box(result->num_rules));
  for (unsigned int i = 0; i < result->num_rules; i++) {
    struct sss_sudo_rule *rule = &result->rules[i];
    int error = EPROTO;
    if (rule->num_attrs && !rule->attrs) {
      lean_dec(rules);
      return error;
    }
    lean_object *attrs = lean_mk_empty_array_with_capacity(lean_box(rule->num_attrs));
    for (unsigned int j = 0; j < rule->num_attrs; j++) {
      struct sss_sudo_attr *attr = &rule->attrs[j];
      lean_object *name = ls_string(attr->name);
      if (!name) {
        error = attr->name ? EILSEQ : EPROTO;
        goto bad_rule;
      }
      char **values = NULL;
      /* Isolate this attribute so duplicate names retain their actual values;
       * libsss_sudo otherwise returns only the first case-insensitive match. */
      struct sss_sudo_rule single = {1, attr};
      error = api->get_values(&single, attr->name, &values);
      if (error != 0 || !values) {
        if (values) api->free_values(values);
        lean_dec(name);
        if (!error) error = EPROTO;
        goto bad_rule;
      }
      lean_object *copied = lean_mk_empty_array_with_capacity(lean_box(attr->num_values));
      for (size_t k = 0; values[k]; k++) {
        lean_object *value = ls_string(values[k]);
        if (!value) {
          api->free_values(values);
          lean_dec(copied);
          lean_dec(name);
          error = EILSEQ;
          goto bad_rule;
        }
        copied = lean_array_push(copied, value);
      }
      api->free_values(values);
      attrs = lean_array_push(attrs, ls_pair(name, copied));
    }
    rules = lean_array_push(rules, attrs);
    continue;
  bad_rule:
    lean_dec(attrs);
    lean_dec(rules);
    return error;
  }
  *out = rules;
  return 0;
}

LEAN_EXPORT lean_obj_res leansudo_sss_query(uint32_t uid, b_lean_obj_arg user,
    lean_obj_arg world) {
  (void)world;
  const char *username = lean_string_cstr(user);
  if (!*username || strlen(username) != lean_string_size(user) - 1)
    return failure("username", EINVAL);
  void *handle = open_library();
  if (!handle)
    return lean_io_result_mk_ok(ls_pair(lean_mk_empty_array(), lean_mk_empty_array()));
  struct sss_api api = {0};
  if (!load_api(handle, &api)) {
    dlclose(handle);
    return failure("library ABI", ENOSYS);
  }

  lean_object *defaults = NULL, *rules = NULL;
  struct sss_sudo_result *result = NULL;
  char *domain = NULL;
  const char *operation = "defaults query";
  int error = 0;
  for (unsigned query = 0; query < 2; query++) {
    operation = query ? "rules query" : "defaults query";
    uint32_t server_error = 0;
    errno = 0;
    int rc = query ?
      api.send_recv((uid_t)uid, username, domain, &server_error, &result) :
      api.send_recv_defaults((uid_t)uid, username, &server_error, &domain, &result);
    int saved_errno = errno;
    if (rc != 0) {
      error = request_error(rc, server_error, saved_errno);
      if (!unavailable(error)) goto done;
      error = 0;
    } else if (server_error == 0) {
      error = copy_result(&api, result, query ? &rules : &defaults);
      if (error) goto done;
    } else if (server_error != ENOENT) {
      error = server_error <= INT_MAX ? (int)server_error : EIO;
      goto done;
    }
    if (!query) {
      api.free_result(result);
      result = NULL;
    }
  }

done:
  api.free_result(result);
  free(domain);
  dlclose(handle);
  if (error) {
    if (defaults) lean_dec(defaults);
    if (rules) lean_dec(rules);
    return failure(operation, error);
  }
  return lean_io_result_mk_ok(ls_pair(defaults ? defaults : lean_mk_empty_array(),
    rules ? rules : lean_mk_empty_array()));
}
