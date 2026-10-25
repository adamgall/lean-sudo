#include "shim.h"
#include <arpa/inet.h>
#include <errno.h>
#include <glob.h>
#include <ifaddrs.h>
#include <limits.h>
#include <linux/audit.h>
#include <locale.h>
#include <netdb.h>
#include <net/if.h>
#include <stddef.h>
#include <poll.h>
#include <regex.h>
#include <sys/socket.h>
#include <linux/netlink.h>
#include <unistd.h>

#ifndef AUDIT_USER_CMD
#define AUDIT_USER_CMD 1123
#endif

static lean_object *extra_status(int status, uintptr_t pointer) {
    return ls_pair(lean_box_uint32((uint32_t)status), lean_box_usize(pointer));
}

LEAN_EXPORT lean_obj_res leansudo_extra_signal_description(uint32_t signal) {
    return ls_ok(lean_mk_string(strsignal((int)signal)));
}

LEAN_EXPORT lean_obj_res leansudo_extra_domain(void) {
    char value[256] = {0};
    int status = getdomainname(value, sizeof value - 1);
    return ls_ok(ls_pair(lean_box_uint32(status < 0 ? errno : 0), lean_mk_string(value)));
}

LEAN_EXPORT lean_obj_res leansudo_extra_locale_new(b_lean_obj_arg name) {
    locale_t value = newlocale(LC_ALL_MASK, lean_string_cstr(name), (locale_t)0);
    return ls_ok(extra_status(value ? 0 : errno, (uintptr_t)value));
}

LEAN_EXPORT lean_obj_res leansudo_extra_locale_use(size_t value) {
    locale_t previous = uselocale((locale_t)value);
    return ls_ok(extra_status(previous ? 0 : errno, (uintptr_t)previous));
}

LEAN_EXPORT lean_obj_res leansudo_extra_locale_free(size_t value) {
    freelocale((locale_t)value);
    return ls_unit();
}

LEAN_EXPORT lean_obj_res leansudo_extra_regex_alloc(void) {
    void *value = calloc(1, sizeof(regex_t));
    if (!value) return ls_error("unable to allocate regular expression");
    return ls_ok(lean_box_usize((uintptr_t)value));
}

LEAN_EXPORT lean_obj_res leansudo_extra_free(size_t value) {
    free((void *)value);
    return ls_unit();
}

LEAN_EXPORT lean_obj_res leansudo_extra_regex_compile(size_t value,
    b_lean_obj_arg pattern, uint32_t flags) {
    return ls_ok(lean_box_uint32(regcomp((regex_t *)value, lean_string_cstr(pattern), flags)));
}

LEAN_EXPORT lean_obj_res leansudo_extra_regex_error(uint32_t status,
    size_t value) {
    char message[256];
    regerror(status, (regex_t *)value, message, sizeof message);
    return ls_ok(lean_mk_string(message));
}

LEAN_EXPORT lean_obj_res leansudo_extra_regex_exec(size_t value,
    b_lean_obj_arg text) {
    return ls_ok(lean_box_uint32(regexec((regex_t *)value, lean_string_cstr(text), 0, NULL, 0)));
}

LEAN_EXPORT lean_obj_res leansudo_extra_regex_free(size_t value) {
    regfree((regex_t *)value);
    return ls_unit();
}

LEAN_EXPORT lean_obj_res leansudo_extra_glob_alloc(void) {
    void *value = calloc(1, sizeof(glob_t));
    if (!value) return ls_error("unable to allocate command glob");
    return ls_ok(lean_box_usize((uintptr_t)value));
}

LEAN_EXPORT lean_obj_res leansudo_extra_glob(size_t value,
    b_lean_obj_arg pattern) {
    return ls_ok(lean_box_uint32(glob(lean_string_cstr(pattern),
        GLOB_NOSORT, NULL, (glob_t *)value)));
}

LEAN_EXPORT lean_obj_res leansudo_extra_glob_count(size_t value) {
    return ls_ok(lean_box_usize(((glob_t *)value)->gl_pathc));
}

LEAN_EXPORT lean_obj_res leansudo_extra_glob_path(size_t value, size_t index) {
    return ls_ok(lean_mk_string(((glob_t *)value)->gl_pathv[index]));
}

LEAN_EXPORT lean_obj_res leansudo_extra_glob_free(size_t value) {
    globfree((glob_t *)value);
    return ls_unit();
}

LEAN_EXPORT lean_obj_res leansudo_extra_interfaces(void) {
    struct ifaddrs *value = NULL;
    int status = getifaddrs(&value);
    return ls_ok(extra_status(status < 0 ? errno : 0, (uintptr_t)value));
}

LEAN_EXPORT lean_obj_res leansudo_extra_interfaces_free(size_t value) {
    freeifaddrs((struct ifaddrs *)value);
    return ls_unit();
}

LEAN_EXPORT lean_obj_res leansudo_extra_interface_next(size_t value) {
    return ls_ok(lean_box_usize((uintptr_t)((struct ifaddrs *)value)->ifa_next));
}

LEAN_EXPORT lean_obj_res leansudo_extra_interface_address(size_t value) {
    return ls_ok(lean_box_usize((uintptr_t)((struct ifaddrs *)value)->ifa_addr));
}

LEAN_EXPORT lean_obj_res leansudo_extra_interface_mask(size_t value) {
    return ls_ok(lean_box_usize((uintptr_t)((struct ifaddrs *)value)->ifa_netmask));
}

LEAN_EXPORT lean_obj_res leansudo_extra_interface_flags(size_t value) {
    return ls_ok(lean_box_uint32(((struct ifaddrs *)value)->ifa_flags));
}

LEAN_EXPORT lean_obj_res leansudo_extra_address_family(size_t value) {
    return ls_ok(lean_box_uint32(((struct sockaddr *)value)->sa_family));
}

LEAN_EXPORT lean_obj_res leansudo_extra_address_v4(size_t value) {
    return ls_ok(lean_box_usize((uintptr_t)&((struct sockaddr_in *)value)->sin_addr));
}

LEAN_EXPORT lean_obj_res leansudo_extra_address_v6(size_t value) {
    return ls_ok(lean_box_usize((uintptr_t)&((struct sockaddr_in6 *)value)->sin6_addr));
}

LEAN_EXPORT lean_obj_res leansudo_extra_address_text(uint32_t family,
    size_t value) {
    char text[INET6_ADDRSTRLEN];
    if (!inet_ntop(family, (void *)value, text, sizeof text)) return ls_ok(lean_box(0));
    lean_object *out = lean_alloc_ctor(1, 1, 0);
    lean_ctor_set(out, 0, lean_mk_string(text));
    return ls_ok(out);
}

LEAN_EXPORT lean_obj_res leansudo_extra_hostname(b_lean_obj_arg host) {
    struct addrinfo hints = {.ai_flags = AI_CANONNAME, .ai_family = AF_UNSPEC};
    struct addrinfo *value = NULL;
    int status = getaddrinfo(lean_string_cstr(host), NULL, &hints, &value);
    return ls_ok(extra_status(status, (uintptr_t)value));
}

LEAN_EXPORT lean_obj_res leansudo_extra_hostname_name(size_t value) {
    const char *name = ((struct addrinfo *)value)->ai_canonname;
    if (!name) return ls_ok(lean_box(0));
    lean_object *out = lean_alloc_ctor(1, 1, 0);
    lean_ctor_set(out, 0, lean_mk_string(name));
    return ls_ok(out);
}

LEAN_EXPORT lean_obj_res leansudo_extra_hostname_error(uint32_t status) {
    return ls_ok(lean_mk_string(gai_strerror((int32_t)status)));
}

LEAN_EXPORT lean_obj_res leansudo_extra_hostname_free(size_t value) {
    freeaddrinfo((struct addrinfo *)value);
    return ls_unit();
}

LEAN_EXPORT lean_obj_res leansudo_extra_socket(uint32_t family,
    uint32_t type, uint32_t protocol) {
    int fd = socket(family, type, protocol);
    return ls_ok(ls_pair(lean_box_uint32(fd < 0 ? errno : 0), lean_box_uint32((uint32_t)fd)));
}

LEAN_EXPORT lean_obj_res leansudo_extra_close(uint32_t fd) {
    int status = close(fd);
    return ls_ok(lean_box_uint32(status < 0 ? errno : 0));
}

LEAN_EXPORT lean_obj_res leansudo_extra_cwd(void) {
    char value[4096];
    if (!getcwd(value, sizeof value)) return ls_ok(lean_box(0));
    lean_object *out = lean_alloc_ctor(1, 1, 0);
    size_t count = strlen(value);
    lean_object *bytes = lean_alloc_sarray(1, count, count);
    memcpy(lean_sarray_cptr(bytes), value, count);
    lean_ctor_set(out, 0, bytes);
    return ls_ok(out);
}

LEAN_EXPORT lean_obj_res leansudo_extra_readlink(b_lean_obj_arg path) {
    char value[4096];
    ssize_t count = readlink(lean_string_cstr(path), value, sizeof value - 1);
    if (count < 0) return ls_ok(lean_box(0));
    lean_object *bytes = lean_alloc_sarray(1, count, count);
    memcpy(lean_sarray_cptr(bytes), value, count);
    lean_object *out = lean_alloc_ctor(1, 1, 0);
    lean_ctor_set(out, 0, bytes);
    return ls_ok(out);
}

LEAN_EXPORT lean_obj_res leansudo_extra_netlink_send(uint32_t fd,
    b_lean_obj_arg bytes) {
    struct sockaddr_nl kernel = {.nl_family = AF_NETLINK};
    ssize_t count = sendto(fd, lean_sarray_cptr(bytes), lean_sarray_size(bytes), 0,
        (struct sockaddr *)&kernel, sizeof kernel);
    return ls_ok(lean_box_uint32(count < 0 ? errno : 0));
}

LEAN_EXPORT lean_obj_res leansudo_extra_poll(uint32_t fd, uint32_t timeout) {
    struct pollfd item = {.fd = fd, .events = POLLIN};
    int status = poll(&item, 1, (int32_t)timeout);
    int error = status < 0 ? errno : 0;
    return ls_ok(ls_pair(lean_box_uint32((uint32_t)status), lean_box_uint32(error)));
}

LEAN_EXPORT lean_obj_res leansudo_extra_netlink_receive(uint32_t fd) {
    unsigned char bytes[4096];
    struct sockaddr_nl sender = {0};
    socklen_t size = sizeof sender;
    ssize_t count = recvfrom(fd, bytes, sizeof bytes, 0, (struct sockaddr *)&sender, &size);
    if (count < 0) return ls_ok(lean_box(0));
    lean_object *data = lean_alloc_sarray(1, count, count);
    memcpy(lean_sarray_cptr(data), bytes, count);
    lean_object *out = lean_alloc_ctor(1, 1, 0);
    lean_ctor_set(out, 0, ls_pair(lean_box_uint32(sender.nl_pid), data));
    return ls_ok(out);
}

LEAN_EXPORT uint8_t leansudo_extra_little_endian(lean_obj_arg unit) {
    (void)unit;
    return __BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__;
}

LEAN_EXPORT lean_obj_res leansudo_extra_constants(lean_obj_arg unit) {
    (void)unit;
    lean_object *out = lean_alloc_ctor(0, 0, 39 * sizeof(uint32_t));
#define EXTRA_CONSTANT(index, value) \
    lean_ctor_set_uint32(out, (index) * sizeof(uint32_t), (uint32_t)(value))
    EXTRA_CONSTANT(0, REG_EXTENDED);
    EXTRA_CONSTANT(1, REG_NOSUB);
    EXTRA_CONSTANT(2, REG_ICASE);
    EXTRA_CONSTANT(3, REG_NOMATCH);
    EXTRA_CONSTANT(4, REG_BADBR);
    EXTRA_CONSTANT(5, REG_BADRPT);
    EXTRA_CONSTANT(6, GLOB_NOMATCH);
    EXTRA_CONSTANT(7, IFF_UP);
    EXTRA_CONSTANT(8, IFF_LOOPBACK);
    EXTRA_CONSTANT(9, AF_INET);
    EXTRA_CONSTANT(10, AF_INET6);
    EXTRA_CONSTANT(11, AF_NETLINK);
    EXTRA_CONSTANT(12, SOCK_RAW);
    EXTRA_CONSTANT(13, SOCK_CLOEXEC);
    EXTRA_CONSTANT(14, NETLINK_AUDIT);
    EXTRA_CONSTANT(15, ENOMEM);
    EXTRA_CONSTANT(16, EAFNOSUPPORT);
    EXTRA_CONSTANT(17, EPROTONOSUPPORT);
    EXTRA_CONSTANT(18, EINVAL);
    EXTRA_CONSTANT(19, ECONNREFUSED);
    EXTRA_CONSTANT(20, AUDIT_USER_CMD);
    EXTRA_CONSTANT(21, NLM_F_REQUEST);
    EXTRA_CONSTANT(22, NLM_F_ACK);
    EXTRA_CONSTANT(23, NLMSG_ERROR);
    EXTRA_CONSTANT(24, NLMSG_HDRLEN);
    EXTRA_CONSTANT(25, offsetof(struct nlmsghdr, nlmsg_len));
    EXTRA_CONSTANT(26, offsetof(struct nlmsghdr, nlmsg_type));
    EXTRA_CONSTANT(27, offsetof(struct nlmsghdr, nlmsg_flags));
    EXTRA_CONSTANT(28, offsetof(struct nlmsghdr, nlmsg_seq));
    EXTRA_CONSTANT(29, offsetof(struct nlmsghdr, nlmsg_pid));
    EXTRA_CONSTANT(30, sizeof(((struct nlmsghdr *)0)->nlmsg_len));
    EXTRA_CONSTANT(31, sizeof(((struct nlmsghdr *)0)->nlmsg_type));
    EXTRA_CONSTANT(32, sizeof(((struct nlmsghdr *)0)->nlmsg_flags));
    EXTRA_CONSTANT(33, sizeof(((struct nlmsghdr *)0)->nlmsg_seq));
    EXTRA_CONSTANT(34, sizeof(((struct nlmsghdr *)0)->nlmsg_pid));
    EXTRA_CONSTANT(35, NLMSG_LENGTH(sizeof(struct nlmsgerr)));
    EXTRA_CONSTANT(36, NLMSG_HDRLEN + offsetof(struct nlmsgerr, error));
    EXTRA_CONSTANT(37, sizeof(((struct nlmsgerr *)0)->error));
    EXTRA_CONSTANT(38, INT_MAX);
#undef EXTRA_CONSTANT
    return out;
}
