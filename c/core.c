#include "shim.h"
#include <fcntl.h>
#include <sys/stat.h>
#include <unistd.h>

LEAN_EXPORT lean_obj_res lean_internal_set_thread_stack_size(size_t size);

__attribute__((constructor(101))) static void core_bootstrap(void) {
    for (int fd = 0; fd <= 2; fd++)
        if (fcntl(fd, F_GETFL) == -1 && open("/dev/null", O_RDWR) != fd) _exit(1);
    lean_internal_set_thread_stack_size(64 * 1024 * 1024);
}

LEAN_EXPORT lean_obj_res lean_sudo_getuid(void) {
    return ls_ok(lean_uint64_to_nat(getuid()));
}

LEAN_EXPORT lean_obj_res lean_sudo_geteuid(void) {
    return ls_ok(lean_uint64_to_nat(geteuid()));
}

LEAN_EXPORT lean_obj_res lean_sudo_getgid(void) {
    return ls_ok(lean_uint64_to_nat(getgid()));
}

LEAN_EXPORT lean_obj_res lean_sudo_getegid(void) {
    return ls_ok(lean_uint64_to_nat(getegid()));
}

LEAN_EXPORT lean_obj_res lean_sudo_isatty(uint32_t fd) {
    return ls_ok(lean_box(isatty((int)fd) ? 1 : 0));
}

LEAN_EXPORT lean_obj_res lean_sudo_umask(uint32_t mask) {
    return ls_ok(lean_box_uint32((uint32_t)umask((mode_t)mask)));
}
