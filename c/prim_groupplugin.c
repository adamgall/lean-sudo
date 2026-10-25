#include "shim.h"
#include "sudo_plugin.h"
#include <pwd.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>

static lean_object *group_logger;

static int group_printf(int type, const char *fmt, ...) {
  if (!group_logger) return -1;
  va_list ap, copied;
  va_start(ap, fmt);
  va_copy(copied, ap);
  int length = vsnprintf(NULL, 0, fmt, copied);
  va_end(copied);
  if (length < 0) { va_end(ap); return length; }
  char *message = malloc((size_t)length + 1);
  if (!message) { va_end(ap); return -1; }
  vsnprintf(message, (size_t)length + 1, fmt, ap);
  va_end(ap);
  lean_inc(group_logger);
  lean_object *result = lean_apply_3(group_logger, lean_box_uint32((uint32_t)type),
    lean_mk_string(message), lean_box(0));
  free(message);
  int rc = lean_io_result_is_ok(result) ?
    (int32_t)lean_unbox_uint32(lean_io_result_get_value(result)) : -1;
  lean_dec(result);
  return rc;
}
LEAN_EXPORT lean_obj_res ls_group_logger(lean_obj_arg callback) {
  lean_mark_mt(callback);
  if (group_logger) lean_dec(group_logger);
  group_logger = callback;
  return lean_io_result_mk_ok(lean_box(0));
}
LEAN_EXPORT lean_obj_res ls_group_version(uint64_t ptr) {
  struct sudoers_group_plugin *plugin = (void *)(uintptr_t)ptr;
  return lean_io_result_mk_ok(lean_box_uint32(plugin->version));
}
LEAN_EXPORT lean_obj_res ls_group_functions(uint64_t ptr) {
  struct sudoers_group_plugin *plugin = (void *)(uintptr_t)ptr;
  return lean_io_result_mk_ok(ls_pair(lean_box_uint64((uintptr_t)plugin->init),
    ls_pair(lean_box_uint64((uintptr_t)plugin->query),
      lean_box_uint64((uintptr_t)plugin->cleanup))));
}
LEAN_EXPORT lean_obj_res ls_group_init(uint64_t fn, uint64_t args) {
  int rc = ((int (*)(int, sudo_printf_t, char *const []))(uintptr_t)fn)(
    1 << 16, group_printf, (char **)(uintptr_t)args);
  return lean_io_result_mk_ok(lean_box_uint32((uint32_t)rc));
}
LEAN_EXPORT lean_obj_res ls_group_query(uint64_t fn, b_lean_obj_arg user,
    b_lean_obj_arg group, uint64_t passwd) {
  int rc = ((int (*)(const char *, const char *, const struct passwd *))(uintptr_t)fn)(
    lean_string_cstr(user), lean_string_cstr(group), (void *)(uintptr_t)passwd);
  return lean_io_result_mk_ok(lean_box_uint32((uint32_t)rc));
}
LEAN_EXPORT lean_obj_res ls_group_cleanup(uint64_t fn) {
  ((void (*)(void))(uintptr_t)fn)();
  return lean_io_result_mk_ok(lean_box(0));
}
LEAN_EXPORT size_t ls_group_passwd_size(lean_obj_arg unit) {
  (void)unit;
  return sizeof(struct passwd);
}
LEAN_EXPORT lean_obj_res ls_group_passwd(b_lean_obj_arg name, uint64_t record,
    uint64_t buffer, size_t size) {
  struct passwd *result = NULL;
  int error = getpwnam_r(lean_string_cstr(name), (void *)(uintptr_t)record,
    (void *)(uintptr_t)buffer, size, &result);
  return lean_io_result_mk_ok(ls_pair(lean_box_uint32(error), lean_box(result != NULL)));
}
