#include "shim.h"
#include <netdb.h>

static const char *optional(b_lean_obj_arg value) {
    return lean_is_scalar(value) ? NULL : lean_string_cstr(lean_ctor_get(value, 0));
}

LEAN_EXPORT lean_obj_res leansudo_sys_netgroup(b_lean_obj_arg group,
    b_lean_obj_arg host, b_lean_obj_arg user, b_lean_obj_arg domain) {
    int result = innetgr(lean_string_cstr(group), optional(host), optional(user), optional(domain));
    return lean_io_result_mk_ok(lean_box(result != 0));
}
