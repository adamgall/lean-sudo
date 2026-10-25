#ifndef _GNU_SOURCE
#define _GNU_SOURCE
#endif
#include <lean/lean.h>
#include <errno.h>
#include <stdint.h>
#include <string.h>
#include <unistd.h>

LEAN_EXPORT lean_obj_res leansudo_visudo_default_path(void) {
    char buffer[4096] = {0};
    size_t length = confstr(_CS_PATH, buffer, sizeof(buffer));
    int error = length == 0 ? errno : 0;
    lean_object *value = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(value, 0, lean_box_usize(length));
    lean_ctor_set(value, 1, lean_mk_string_from_bytes(buffer,
        strnlen(buffer, sizeof(buffer) - 1)));
    lean_object *result = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(result, 0, lean_box_uint32(error));
    lean_ctor_set(result, 1, value);
    return lean_io_result_mk_ok(result);
}

LEAN_EXPORT uint32_t leansudo_visudo_ENOTDIR(lean_obj_arg unit) {
    (void)unit;
    return ENOTDIR;
}

LEAN_EXPORT uint32_t leansudo_visudo_ESTALE(lean_obj_arg unit) {
    (void)unit;
    return ESTALE;
}

LEAN_EXPORT uint32_t leansudo_visudo_ENODEV(lean_obj_arg unit) {
    (void)unit;
    return ENODEV;
}
