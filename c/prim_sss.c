#include "shim.h"
#include <errno.h>
#include <stdint.h>
#include <sys/types.h>

struct sss_sudo_attr { char *name; char **values; unsigned int num_values; };
struct sss_sudo_rule { unsigned int num_attrs; struct sss_sudo_attr *attrs; };
struct sss_sudo_result { unsigned int num_rules; struct sss_sudo_rule *rules; };

LEAN_EXPORT lean_obj_res ls_sss_defaults(uint64_t fn, uint32_t uid,
    b_lean_obj_arg user) {
  uint32_t error = 0;
  char *domain = NULL;
  struct sss_sudo_result *result = NULL;
  errno = 0;
  int rc = ((int (*)(uid_t, const char *, uint32_t *, char **,
    struct sss_sudo_result **))(uintptr_t)fn)(uid, lean_string_cstr(user),
      &error, &domain, &result);
  int saved = errno;
  return lean_io_result_mk_ok(ls_pair(ls_pair(lean_box_uint32(rc), lean_box_uint32(saved)),
    ls_pair(lean_box_uint32(error), ls_pair(lean_box_uint64((uintptr_t)domain),
      lean_box_uint64((uintptr_t)result)))));
}
LEAN_EXPORT lean_obj_res ls_sss_rules(uint64_t fn, uint32_t uid,
    b_lean_obj_arg user, uint64_t domain) {
  uint32_t error = 0;
  struct sss_sudo_result *result = NULL;
  errno = 0;
  int rc = ((int (*)(uid_t, const char *, const char *, uint32_t *,
    struct sss_sudo_result **))(uintptr_t)fn)(uid, lean_string_cstr(user),
      (const char *)(uintptr_t)domain, &error, &result);
  int saved = errno;
  return lean_io_result_mk_ok(ls_pair(ls_pair(lean_box_uint32(rc), lean_box_uint32(saved)),
    ls_pair(lean_box_uint32(error), lean_box_uint64((uintptr_t)result))));
}
LEAN_EXPORT lean_obj_res ls_sss_free_result(uint64_t fn, uint64_t ptr) {
  ((void (*)(struct sss_sudo_result *))(uintptr_t)fn)((void *)(uintptr_t)ptr);
  return lean_io_result_mk_ok(lean_box(0));
}
LEAN_EXPORT lean_obj_res ls_sss_result(uint64_t ptr) {
  struct sss_sudo_result *result = (void *)(uintptr_t)ptr;
  return lean_io_result_mk_ok(ls_pair(lean_box_uint32(result->num_rules),
    lean_box_uint64((uintptr_t)result->rules)));
}
LEAN_EXPORT lean_obj_res ls_sss_rule(uint64_t ptr, uint32_t index) {
  struct sss_sudo_rule *rule = &((struct sss_sudo_rule *)(uintptr_t)ptr)[index];
  return lean_io_result_mk_ok(ls_pair(lean_box_uint32(rule->num_attrs),
    lean_box_uint64((uintptr_t)rule->attrs)));
}
LEAN_EXPORT lean_obj_res ls_sss_attr(uint64_t ptr, uint32_t index) {
  struct sss_sudo_attr *attr = &((struct sss_sudo_attr *)(uintptr_t)ptr)[index];
  return lean_io_result_mk_ok(ls_pair(lean_box_uint64((uintptr_t)attr->name),
    lean_box_uint32(attr->num_values)));
}
LEAN_EXPORT lean_obj_res ls_sss_values(uint64_t fn, uint64_t ptr, uint32_t index) {
  struct sss_sudo_attr *attr = &((struct sss_sudo_attr *)(uintptr_t)ptr)[index];
  struct sss_sudo_rule single = {1, attr};
  char **values = NULL;
  int rc = ((int (*)(struct sss_sudo_rule *, const char *, char ***))(uintptr_t)fn)(
    &single, attr->name, &values);
  return lean_io_result_mk_ok(ls_pair(lean_box_uint32(rc),
    lean_box_uint64((uintptr_t)values)));
}
LEAN_EXPORT lean_obj_res ls_sss_free_values(uint64_t fn, uint64_t ptr) {
  ((void (*)(char **))(uintptr_t)fn)((void *)(uintptr_t)ptr);
  return lean_io_result_mk_ok(lean_box(0));
}
