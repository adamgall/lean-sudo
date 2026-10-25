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
static inline const char *ls_cstr(b_lean_obj_arg value) {
    const char *s = lean_string_cstr(value);
    return strlen(s) == lean_string_size(value) - 1 ? s : NULL;
}
static inline lean_object *ls_pair(lean_obj_arg a, lean_obj_arg b) {
    lean_object *out = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(out, 0, a);
    lean_ctor_set(out, 1, b);
    return out;
}
__attribute__((format(printf, 1, 2)))
lean_obj_res ls_errorf(const char *format, ...);
lean_obj_res ls_errno(int error);
bool ls_utf8_valid(const char *s, size_t n);
lean_object *ls_string_n(const char *s, size_t n);
lean_object *ls_string(const char *s);
void ls_strv_free(char **v);
char **ls_strv(b_lean_obj_arg array, bool copy);
size_t ls_strv_len(char *const *v);
int ls_transfer(int fd, void *buffer, size_t size, int sending);
int ls_write_all(int fd, const void *buffer, size_t size);
int64_t ls_mono_ms(void);
int ls_close_from(int fd);
int ls_compare_gid(const void *a, const void *b);
int ls_drop_credentials(uid_t uid, gid_t gid, const gid_t *groups, size_t n, gid_t *verify);
bool ls_trace_supported(void);
struct ls_symbol { const char *name; void *slot; };
const char *ls_dlsyms(void *handle, const struct ls_symbol *symbols, size_t n);
#endif
