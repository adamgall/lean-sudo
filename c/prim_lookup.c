#include "shim.h"
#include <errno.h>
#include <limits.h>
#include <signal.h>
#include <sys/stat.h>

LEAN_EXPORT uint32_t leansudo_lookup_missing(b_lean_obj_arg unit) { return ENOENT; }
LEAN_EXPORT uint32_t leansudo_lookup_not_directory(b_lean_obj_arg unit) { return ENOTDIR; }
LEAN_EXPORT uint32_t leansudo_lookup_denied(b_lean_obj_arg unit) { return EACCES; }
LEAN_EXPORT uint32_t leansudo_lookup_not_permitted(b_lean_obj_arg unit) { return EPERM; }
LEAN_EXPORT uint32_t leansudo_lookup_loop(b_lean_obj_arg unit) { return ELOOP; }
LEAN_EXPORT uint32_t leansudo_lookup_invalid(b_lean_obj_arg unit) { return EINVAL; }
LEAN_EXPORT uint32_t leansudo_lookup_io(b_lean_obj_arg unit) { return EIO; }
LEAN_EXPORT uint32_t leansudo_lookup_interrupted(b_lean_obj_arg unit) { return EINTR; }
LEAN_EXPORT uint32_t leansudo_lookup_kill(b_lean_obj_arg unit) { return SIGKILL; }
LEAN_EXPORT uint32_t leansudo_lookup_int_max(b_lean_obj_arg unit) { return INT_MAX; }
LEAN_EXPORT uint32_t leansudo_lookup_exec_bits(b_lean_obj_arg unit) {
    return S_IXUSR | S_IXGRP | S_IXOTH;
}
