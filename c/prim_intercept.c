#ifndef _GNU_SOURCE
#define _GNU_SOURCE
#endif
#include "shim.h"
#include <errno.h>
#include <fcntl.h>
#include <poll.h>
#include <signal.h>
#include <limits.h>
#include <stddef.h>
#include <netinet/in.h>
#include <netinet/tcp.h>
#include <sys/socket.h>
#include <sys/stat.h>
#include <sys/wait.h>
#include <unistd.h>
#if defined(__linux__)
#include <elf.h>
#include <linux/binfmts.h>
#include <linux/audit.h>
#include <linux/filter.h>
#include <linux/seccomp.h>
#include <sys/syscall.h>
#include <sys/ptrace.h>
#include <sys/random.h>
#include <sys/uio.h>
#if defined(__x86_64__)
#include <sys/user.h>
typedef struct user_regs_struct intercept_native_regs;
typedef struct {
    uint32_t ebx, ecx, edx, esi, edi, ebp, eax, ds, es, fs, gs;
    uint32_t orig_eax, eip, cs, eflags, esp, ss;
} intercept_compat_regs;
#elif defined(__aarch64__)
#include <asm/ptrace.h>
typedef struct user_pt_regs intercept_native_regs;
typedef struct { uint32_t regs[18]; } intercept_compat_regs;
#endif
#endif

static lean_object *buffer(size_t size) {
    lean_object *out = lean_alloc_sarray(1, size, size);
    return out;
}

uint64_t lean_intercept_constants(uint32_t index) {
    static const uint64_t values[] = {
        sizeof(long), sizeof(uintptr_t), sizeof(uint32_t), INADDR_LOOPBACK,
        AF_INET, SOCK_STREAM, IPPROTO_TCP, TCP_NODELAY,
        POLLIN, POLLOUT, POLLERR, POLLNVAL, POLLHUP,
        S_ISUID | S_ISGID, ENOSYS, EACCES, ECHILD, SIGTRAP,
        sizeof(struct sockaddr_in), offsetof(struct sockaddr_in, sin_family),
        sizeof(((struct sockaddr_in *)0)->sin_family),
        offsetof(struct sockaddr_in, sin_port), sizeof(((struct sockaddr_in *)0)->sin_port),
        offsetof(struct sockaddr_in, sin_addr), sizeof(((struct sockaddr_in *)0)->sin_addr),
#if defined(__linux__)
        __WALL,
#else
        0,
#endif
        0xff, 0x7f, 0x7f, 8, 16, 0x80,
#if defined(__linux__) && (defined(__x86_64__) || defined(__aarch64__))
        NT_PRSTATUS,
#if defined(__aarch64__)
        0x404,
#else
        0,
#endif
        PTRACE_PEEKDATA, PTRACE_POKEDATA, PTRACE_SYSCALL, PTRACE_CONT, PTRACE_SEIZE,
        PTRACE_O_TRACESECCOMP | PTRACE_O_TRACEEXEC | PTRACE_O_TRACEFORK |
            PTRACE_O_TRACEVFORK | PTRACE_O_TRACECLONE | PTRACE_O_TRACESYSGOOD,
        PTRACE_LISTEN, PTRACE_DETACH, PTRACE_INTERRUPT, PTRACE_EVENT_EXEC,
        PTRACE_EVENT_FORK, PTRACE_EVENT_VFORK, PTRACE_EVENT_CLONE,
        PTRACE_EVENT_SECCOMP, PTRACE_EVENT_STOP,
        sizeof(intercept_native_regs), sizeof(intercept_compat_regs),
#if defined(__x86_64__)
        offsetof(intercept_native_regs, rdi), offsetof(intercept_native_regs, rsi),
        offsetof(intercept_native_regs, rdx),
        offsetof(intercept_compat_regs, ebx), offsetof(intercept_compat_regs, ecx),
        offsetof(intercept_compat_regs, edx),
        offsetof(intercept_native_regs, rbx), offsetof(intercept_native_regs, rcx),
        offsetof(intercept_native_regs, rdx),
        offsetof(intercept_native_regs, rsp), offsetof(intercept_compat_regs, esp),
        offsetof(intercept_native_regs, orig_rax), offsetof(intercept_compat_regs, orig_eax),
        offsetof(intercept_native_regs, rax), offsetof(intercept_compat_regs, eax),
        sizeof(((intercept_native_regs *)0)->rax),
        sizeof(((intercept_compat_regs *)0)->eax),
        AUDIT_ARCH_X86_64, AUDIT_ARCH_I386, SYS_execve, SYS_execveat, 11, 358,
        0x40000000U + 520U, 0x40000000U + 545U,
#else
        offsetof(intercept_native_regs, regs[0]), offsetof(intercept_native_regs, regs[1]),
        offsetof(intercept_native_regs, regs[2]),
        offsetof(intercept_compat_regs, regs[0]), offsetof(intercept_compat_regs, regs[1]),
        offsetof(intercept_compat_regs, regs[2]),
        offsetof(intercept_native_regs, regs[0]), offsetof(intercept_native_regs, regs[1]),
        offsetof(intercept_native_regs, regs[2]),
        offsetof(intercept_native_regs, sp), offsetof(intercept_compat_regs, regs[13]),
        offsetof(intercept_native_regs, regs[8]), offsetof(intercept_compat_regs, regs[7]),
        offsetof(intercept_native_regs, regs[0]), offsetof(intercept_compat_regs, regs[0]),
        sizeof(((intercept_native_regs *)0)->regs[0]),
        sizeof(((intercept_compat_regs *)0)->regs[0]),
        AUDIT_ARCH_AARCH64, AUDIT_ARCH_ARM, SYS_execve, SYS_execveat, 11, 387, 0, 0,
#endif
        SECCOMP_RET_TRACE, SECCOMP_RET_ALLOW, SECCOMP_RET_KILL_PROCESS,
        BPF_LD | BPF_W | BPF_ABS, BPF_JMP | BPF_JEQ | BPF_K, BPF_RET | BPF_K,
        offsetof(struct seccomp_data, arch), offsetof(struct seccomp_data, nr),
        sizeof(struct sock_filter),
        offsetof(struct sock_filter, code), sizeof(((struct sock_filter *)0)->code),
        offsetof(struct sock_filter, jt), sizeof(((struct sock_filter *)0)->jt),
        offsetof(struct sock_filter, jf), sizeof(((struct sock_filter *)0)->jf),
        offsetof(struct sock_filter, k), sizeof(((struct sock_filter *)0)->k),
        128, PATH_MAX, BINPRM_BUF_SIZE,
#endif
    };
    return index < sizeof values / sizeof values[0] ? values[index] : 0;
}

lean_obj_res lean_intercept_page_size(void) {
    long size = sysconf(_SC_PAGESIZE);
    return ls_ok(lean_box_uint64((uint64_t)size));
}

lean_obj_res lean_intercept_arch(void) {
#if defined(__linux__) && defined(__x86_64__)
    return ls_ok(lean_box(1));
#elif defined(__linux__) && defined(__aarch64__)
    return ls_ok(lean_box(2));
#else
    return ls_ok(lean_box(0));
#endif
}

lean_obj_res lean_intercept_ptrace(uint32_t request, uint32_t pid,
    uint64_t address, uint64_t data) {
#if defined(__linux__)
    if (request != PTRACE_PEEKDATA && request != PTRACE_POKEDATA &&
        request != PTRACE_SYSCALL && request != PTRACE_CONT && request != PTRACE_SEIZE &&
        request != PTRACE_LISTEN && request != PTRACE_DETACH && request != PTRACE_INTERRUPT)
        return ls_ok(ls_pair(lean_box_uint32(EINVAL), lean_box_uint64(0)));
    errno = 0;
    long result = ptrace(request, pid, (void *)(uintptr_t)address, (void *)(uintptr_t)data);
    int error = errno;
    return ls_ok(ls_pair(lean_box_uint32(error), lean_box_uint64((uint64_t)result)));
#else
    (void)request; (void)pid; (void)address; (void)data;
    return ls_ok(ls_pair(lean_box_uint32(ENOTSUP), lean_box_uint64(0)));
#endif
}

lean_obj_res lean_intercept_regset(uint32_t pid, uint32_t note, uint32_t size) {
#if defined(__linux__)
    lean_object *out = buffer(size);
    struct iovec io = {lean_sarray_cptr(out), size};
    int result = ptrace(PTRACE_GETREGSET, pid, (void *)(uintptr_t)note, &io);
    int error = result < 0 ? errno : 0;
    lean_sarray_set_size(out, result < 0 ? 0 : io.iov_len);
    return ls_ok(ls_pair(lean_box_uint32(error), out));
#else
    (void)pid; (void)note; (void)size;
    return ls_ok(ls_pair(lean_box_uint32(ENOTSUP), buffer(0)));
#endif
}

lean_obj_res lean_intercept_set_regset(uint32_t pid, uint32_t note, b_lean_obj_arg bytes) {
#if defined(__linux__)
    struct iovec io = {lean_sarray_cptr(bytes), lean_sarray_size(bytes)};
    int result = ptrace(PTRACE_SETREGSET, pid, (void *)(uintptr_t)note, &io);
    return ls_ok(lean_box_uint32(result < 0 ? errno : 0));
#else
    (void)pid; (void)note; (void)bytes; return ls_ok(lean_box_uint32(ENOTSUP));
#endif
}

lean_obj_res lean_intercept_event(uint32_t pid) {
#if defined(__linux__)
    unsigned long value = 0;
    int result = ptrace(PTRACE_GETEVENTMSG, pid, NULL, &value);
    int error = result < 0 ? errno : 0;
    return ls_ok(ls_pair(lean_box_uint32(error), lean_box_uint64(value)));
#else
    (void)pid; return ls_ok(ls_pair(lean_box_uint32(ENOTSUP), lean_box_uint64(0)));
#endif
}

lean_obj_res lean_intercept_memory(uint32_t pid, uint64_t address, uint32_t size) {
#if defined(__linux__)
    lean_object *out = buffer(size);
    struct iovec local = {lean_sarray_cptr(out), size};
    struct iovec remote = {(void *)(uintptr_t)address, size};
    ssize_t n = process_vm_readv(pid, &local, 1, &remote, 1, 0);
    int error = n < 0 ? errno : 0;
    lean_sarray_set_size(out, n < 0 ? 0 : (size_t)n);
    return ls_ok(ls_pair(lean_box_uint32(error), out));
#else
    (void)pid; (void)address; (void)size;
    return ls_ok(ls_pair(lean_box_uint32(ENOTSUP), buffer(0)));
#endif
}

lean_obj_res lean_intercept_read(uint32_t fd, uint32_t size) {
    lean_object *out = buffer(size);
    ssize_t n = read(fd, lean_sarray_cptr(out), size);
    int error = n < 0 ? errno : 0;
    lean_sarray_set_size(out, n < 0 ? 0 : (size_t)n);
    return ls_ok(ls_pair(lean_box_uint32(error), out));
}

lean_obj_res lean_intercept_write(uint32_t fd, b_lean_obj_arg bytes, uint32_t offset) {
    if (offset > lean_sarray_size(bytes))
        return ls_ok(lean_box_uint64((uint64_t)-(int64_t)EINVAL));
    ssize_t n = send(fd, lean_sarray_cptr(bytes) + offset,
        lean_sarray_size(bytes) - offset, MSG_NOSIGNAL);
    return ls_ok(lean_box_uint64(n < 0 ? (uint64_t)-(int64_t)errno : (uint64_t)n));
}

lean_obj_res lean_intercept_open(b_lean_obj_arg path, uint32_t flags) {
    int fd = open(lean_string_cstr(path), flags);
    return ls_ok(lean_box_uint32(fd < 0 ? (uint32_t)-errno : (uint32_t)fd));
}

lean_obj_res lean_intercept_close(uint32_t fd) {
    int result = close(fd);
    return ls_ok(lean_box_uint32(result < 0 ? errno : 0));
}

lean_obj_res lean_intercept_readlink(b_lean_obj_arg path, uint32_t size) {
    lean_object *out = buffer(size);
    ssize_t n = readlink(lean_string_cstr(path), (char *)lean_sarray_cptr(out), size);
    int error = n < 0 ? errno : 0;
    lean_sarray_set_size(out, n < 0 ? 0 : (size_t)n);
    return ls_ok(ls_pair(lean_box_uint32(error), out));
}

lean_obj_res lean_intercept_socket(uint32_t family, uint32_t kind) {
    int fd = socket(family, kind, 0);
    return ls_ok(lean_box_uint32(fd < 0 ? (uint32_t)-errno : (uint32_t)fd));
}

lean_obj_res lean_intercept_bind(uint32_t fd, b_lean_obj_arg address) {
    int result = bind(fd, (struct sockaddr *)lean_sarray_cptr(address),
        lean_sarray_size(address));
    return ls_ok(lean_box_uint32(result < 0 ? errno : 0));
}

lean_obj_res lean_intercept_sockname(uint32_t fd) {
    lean_object *out = buffer(sizeof(struct sockaddr_storage));
    socklen_t size = sizeof(struct sockaddr_storage);
    int result = getsockname(fd, (struct sockaddr *)lean_sarray_cptr(out), &size);
    int error = result < 0 ? errno : 0;
    lean_sarray_set_size(out, result < 0 ? 0 : size);
    return ls_ok(ls_pair(lean_box_uint32(error), out));
}

lean_obj_res lean_intercept_listen(uint32_t fd) {
    int result = listen(fd, SOMAXCONN);
    return ls_ok(lean_box_uint32(result < 0 ? errno : 0));
}

lean_obj_res lean_intercept_accept(uint32_t fd) {
    lean_object *out = buffer(sizeof(struct sockaddr_storage));
    socklen_t size = sizeof(struct sockaddr_storage);
    int child = accept(fd, (struct sockaddr *)lean_sarray_cptr(out), &size);
    int result = child < 0 ? -errno : child;
    lean_sarray_set_size(out, child < 0 ? 0 : size);
    return ls_ok(ls_pair(lean_box_uint32((uint32_t)result), out));
}

lean_obj_res lean_intercept_socketpair(void) {
    int pair[2] = {0, 0};
    int result = socketpair(AF_UNIX, SOCK_STREAM, 0, pair);
    int first = result < 0 ? -errno : pair[0];
    return ls_ok(ls_pair(lean_box_uint32((uint32_t)first), lean_box_uint32(pair[1])));
}

lean_obj_res lean_intercept_fcntl(uint32_t fd, uint32_t op, uint32_t value) {
    int result = fcntl(fd, op, value);
    return ls_ok(lean_box_uint32(result < 0 ? (uint32_t)-errno : (uint32_t)result));
}

lean_obj_res lean_intercept_sockopt(uint32_t fd, uint32_t level, uint32_t option,
    uint32_t value) {
    int native = value;
    int result = setsockopt(fd, level, option, &native, sizeof native);
    return ls_ok(lean_box_uint32(result < 0 ? errno : 0));
}

lean_obj_res lean_intercept_poll(uint32_t fd, uint32_t events) {
    struct pollfd p = {(int)fd, (short)events, 0};
    int result = poll(&p, 1, 0);
    int error = result < 0 ? errno : 0;
    return ls_ok(ls_pair(lean_box_uint32(error), lean_box_uint32((uint16_t)p.revents)));
}

lean_obj_res lean_intercept_kill(uint32_t pid, uint32_t signal) {
    int result = kill(pid, signal);
    return ls_ok(lean_box_uint32(result < 0 ? errno : 0));
}

lean_obj_res lean_intercept_wait(void) {
    int status = 0;
#if defined(__linux__)
    pid_t pid = waitpid(-1, &status, __WALL);
#else
    pid_t pid = waitpid(-1, &status, 0);
#endif
    return ls_ok(ls_pair(lean_box_uint64(pid < 0 ? (uint64_t)-(int64_t)errno : (uint64_t)pid),
        lean_box_uint32(status)));
}
