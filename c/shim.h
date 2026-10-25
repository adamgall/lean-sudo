#ifndef LEANSUDO_SHIM_H
#define LEANSUDO_SHIM_H
#include <lean/lean.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <sys/types.h>

static inline lean_obj_res ls_ok(lean_obj_arg value) {
    return lean_io_result_mk_ok(value);
}
static inline lean_obj_res ls_unit(void) { return ls_ok(lean_box(0)); }
static inline lean_obj_res ls_error(const char *message) {
    return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(message)));
}
static inline lean_object *ls_pair(lean_obj_arg a, lean_obj_arg b) {
    lean_object *out = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(out, 0, a);
    lean_ctor_set(out, 1, b);
    return out;
}
#endif
