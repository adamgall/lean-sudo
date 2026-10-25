#include "shim.h"
#include <dlfcn.h>
#include <errno.h>
#include <limits.h>
#include <stdlib.h>
#include <string.h>

LEAN_EXPORT lean_obj_res ls_store_dlopen(b_lean_obj_arg path, uint32_t flags) {
  return lean_io_result_mk_ok(lean_box_uint64((uintptr_t)
    dlopen(lean_string_cstr(path), flags)));
}
LEAN_EXPORT lean_obj_res ls_store_dlsym(uint64_t handle, b_lean_obj_arg name) {
  return lean_io_result_mk_ok(lean_box_uint64((uintptr_t)
    dlsym((void *)(uintptr_t)handle, lean_string_cstr(name))));
}
LEAN_EXPORT lean_obj_res ls_store_dlclose(uint64_t handle) {
  dlclose((void *)(uintptr_t)handle);
  return lean_io_result_mk_ok(lean_box(0));
}
LEAN_EXPORT lean_obj_res ls_store_dlerror(void) {
  const char *error = dlerror();
  if (!error) return lean_io_result_mk_ok(lean_box(0));
  lean_object *some = lean_alloc_ctor(1, 1, 0);
  lean_ctor_set(some, 0, lean_mk_string(error));
  return lean_io_result_mk_ok(some);
}
LEAN_EXPORT lean_obj_res ls_store_free(uint64_t ptr) {
  free((void *)(uintptr_t)ptr);
  return lean_io_result_mk_ok(lean_box(0));
}
LEAN_EXPORT lean_obj_res ls_store_calloc(size_t count, size_t size) {
  return lean_io_result_mk_ok(lean_box_uint64((uintptr_t)calloc(count, size)));
}
LEAN_EXPORT lean_obj_res ls_store_strdup(b_lean_obj_arg text) {
  return lean_io_result_mk_ok(lean_box_uint64((uintptr_t)strdup(lean_string_cstr(text))));
}
LEAN_EXPORT lean_obj_res ls_store_pointer(uint64_t ptr, size_t index) {
  return lean_io_result_mk_ok(lean_box_uint64((uintptr_t)((void **)(uintptr_t)ptr)[index]));
}
LEAN_EXPORT lean_obj_res ls_store_set_pointer(uint64_t ptr, size_t index, uint64_t value) {
  ((void **)(uintptr_t)ptr)[index] = (void *)(uintptr_t)value;
  return lean_io_result_mk_ok(lean_box(0));
}
LEAN_EXPORT lean_obj_res ls_store_bytes(uint64_t ptr) {
  const char *text = (const char *)(uintptr_t)ptr;
  size_t size = strlen(text);
  lean_object *out = lean_alloc_sarray(1, size, size);
  memcpy(lean_sarray_cptr(out), text, size);
  return lean_io_result_mk_ok(out);
}
LEAN_EXPORT lean_obj_res ls_store_strerror(uint32_t error) {
  char buffer[1024];
  return lean_io_result_mk_ok(lean_mk_string(strerror_r(error, buffer, sizeof buffer)));
}
LEAN_EXPORT lean_obj_res ls_store_constants(lean_obj_arg unit) {
  (void)unit;
  lean_object *out = lean_alloc_ctor(0, 0, 23 * sizeof(uint32_t));
  lean_ctor_set_uint32(out, 0 * sizeof(uint32_t), RTLD_NOW);
  lean_ctor_set_uint32(out, 1 * sizeof(uint32_t), RTLD_LAZY);
  lean_ctor_set_uint32(out, 2 * sizeof(uint32_t), RTLD_GLOBAL);
  lean_ctor_set_uint32(out, 3 * sizeof(uint32_t), RTLD_LOCAL);
  lean_ctor_set_uint32(out, 4 * sizeof(uint32_t), EIO);
  lean_ctor_set_uint32(out, 5 * sizeof(uint32_t), ENOENT);
  lean_ctor_set_uint32(out, 6 * sizeof(uint32_t), ECONNREFUSED);
  lean_ctor_set_uint32(out, 7 * sizeof(uint32_t), ECONNRESET);
  lean_ctor_set_uint32(out, 8 * sizeof(uint32_t), ENOTCONN);
  lean_ctor_set_uint32(out, 9 * sizeof(uint32_t), ETIMEDOUT);
  lean_ctor_set_uint32(out, 10 * sizeof(uint32_t), EPIPE);
  lean_ctor_set_uint32(out, 11 * sizeof(uint32_t), EHOSTUNREACH);
  lean_ctor_set_uint32(out, 12 * sizeof(uint32_t), ENETUNREACH);
  lean_ctor_set_uint32(out, 13 * sizeof(uint32_t), ENETDOWN);
  lean_ctor_set_uint32(out, 14 * sizeof(uint32_t), EAGAIN);
  lean_ctor_set_uint32(out, 15 * sizeof(uint32_t), EPROTO);
  lean_ctor_set_uint32(out, 16 * sizeof(uint32_t), EILSEQ);
  lean_ctor_set_uint32(out, 17 * sizeof(uint32_t), EINVAL);
  lean_ctor_set_uint32(out, 18 * sizeof(uint32_t), ENOSYS);
  lean_ctor_set_uint32(out, 19 * sizeof(uint32_t), ENAMETOOLONG);
  lean_ctor_set_uint32(out, 20 * sizeof(uint32_t), INT_MAX);
  lean_ctor_set_uint32(out, 21 * sizeof(uint32_t), sizeof(void *));
  lean_ctor_set_uint32(out, 22 * sizeof(uint32_t), PATH_MAX);
  return out;
}
