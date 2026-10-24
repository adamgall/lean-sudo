/* System lookup oracles: no policy decisions live in this translation unit. */
#include <lean/lean.h>
#include <arpa/inet.h>
#include <errno.h>
#include <glob.h>
#include <ifaddrs.h>
#include <limits.h>
#include <locale.h>
#include <linux/audit.h>
#include <linux/netlink.h>
#include <net/if.h>
#include <netdb.h>
#include <poll.h>
#include <pthread.h>
#include <regex.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/socket.h>
#include <unistd.h>

/* Userspace message type from libaudit.h, part of the stable audit ABI. */
#ifndef AUDIT_USER_CMD
#define AUDIT_USER_CMD 1123
#endif

static lean_obj_res failure(const char *msg) {
  return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(msg)));
}

LEAN_EXPORT lean_obj_res leansudo_sys_domain(lean_obj_arg world) {
  (void)world;
  char name[256] = {0};
  lean_object *out = lean_box(0);
  if (getdomainname(name, sizeof name - 1) == 0 && name[0] &&
      strpbrk(name, " \t\r\n,()") == NULL) {
    out = lean_alloc_ctor(1, 1, 0);
    lean_ctor_set(out, 0, lean_mk_string(name));
  }
  return lean_io_result_mk_ok(out);
}
static const char *optional(b_lean_obj_arg x) {
  return lean_is_scalar(x) ? NULL : lean_string_cstr(lean_ctor_get(x, 0));
}
LEAN_EXPORT lean_obj_res leansudo_sys_interfaces(lean_obj_arg world) {
  (void)world;
  struct ifaddrs *ifs;
  if (getifaddrs(&ifs)) return failure("unable to read network interfaces");
  lean_object *out = lean_mk_empty_array();
  for (struct ifaddrs *i = ifs; i; i = i->ifa_next) {
    if (!i->ifa_addr || !i->ifa_netmask || !(i->ifa_flags & IFF_UP) ||
        (i->ifa_flags & IFF_LOOPBACK)) continue;
    int af = i->ifa_addr->sa_family;
    if (af != AF_INET && af != AF_INET6) continue;
    char addr[INET6_ADDRSTRLEN], mask[INET6_ADDRSTRLEN];
    const void *a = af == AF_INET ? (void *)&((struct sockaddr_in *)i->ifa_addr)->sin_addr : (void *)&((struct sockaddr_in6 *)i->ifa_addr)->sin6_addr;
    const void *m = af == AF_INET ? (void *)&((struct sockaddr_in *)i->ifa_netmask)->sin_addr : (void *)&((struct sockaddr_in6 *)i->ifa_netmask)->sin6_addr;
    if (!inet_ntop(af, a, addr, sizeof addr) || !inet_ntop(af, m, mask, sizeof mask)) continue;
    lean_object *pair = lean_alloc_ctor(0, 2, 0);
    lean_ctor_set(pair, 0, lean_mk_string(addr));
    lean_ctor_set(pair, 1, lean_mk_string(mask));
    out = lean_array_push(out, pair);
  }
  freeifaddrs(ifs);
  return lean_io_result_mk_ok(out);
}
LEAN_EXPORT lean_obj_res leansudo_sys_netgroup(b_lean_obj_arg group, b_lean_obj_arg host, b_lean_obj_arg user, b_lean_obj_arg domain, lean_obj_arg world) {
  (void)world;
  return lean_io_result_mk_ok(lean_box(innetgr(lean_string_cstr(group), optional(host), optional(user), optional(domain)) != 0));
}

/*
 * Repetition validation adapted from sudo lib/util/regex.c (1.9.17p2).
 * Copyright (c) 2023 Todd C. Miller <Todd.Miller@sudo.ws>
 *
 * Permission to use, copy, modify, and distribute this software for any
 * purpose with or without fee is hereby granted, provided that the above
 * copyright notice and this permission notice appear in all copies.
 *
 * THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 * WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
 * ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 * WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
 * ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
 * OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 */
static int regex_number(const char *str, const char **end) {
  int n = 0;
  char c;
  while ((c = *str++) != 0) {
    if (c == '\\' && str[0] >= '0' && str[0] <= '9')
      c = *str++;
    else if (c < '0' || c > '9')
      break;
    int digit = c - '0';
    if (n > INT_MAX / 10 || (n == INT_MAX / 10 && digit > INT_MAX % 10)) {
      n = -1;
      break;
    }
    n = n * 10 + digit;
  }
  *end = str - 1;
  return n;
}

static int regex_repetition(char c) {
  return c == '?' || c == '*' || c == '+' || c == '{';
}

static int regex_check(const char *pattern) {
  const char *p = pattern;
  int upper = 0;
  char c, prev = 0;
  while ((c = *p++) != 0) {
    if (c == '\\' && *p) {
      p++;
      prev = 0;
      continue;
    }
    if (c == '?' || c == '*' || c == '+') {
      if (regex_repetition(prev)) return REG_BADRPT;
    } else if (c == '{') {
      const char *end;
      int lower = regex_number(p, &end);
      if (end[0] == '\\' && end[1] == ',') end++;
      if (*end == ',') upper = regex_number(end + 1, &end);
      p = end;
      if (*p == '}') {
        if (lower < 0 || lower > 255 || upper < 0 || upper > 255) return REG_BADBR;
        if (regex_repetition(prev)) return REG_BADRPT;
        p++;
      } else {
        prev = 0;
        continue;
      }
    }
    prev = c;
  }
  return 0;
}

/* sudoers.c switches to sudoers_locale around lookup, not the invoking
 * user's locale. Use a thread-local locale scope so PAM/libc messages retain
 * the user locale. Cache the default C object for all ordinary lookups. */
static pthread_once_t match_locale_once = PTHREAD_ONCE_INIT;
static locale_t match_c_locale;

static void match_locale_init(void) {
  match_c_locale = newlocale(LC_ALL_MASK, "C", (locale_t)0);
}

static locale_t match_locale_enter(const char *name, locale_t *previous) {
  pthread_once(&match_locale_once, match_locale_init);
  if (!match_c_locale) return (locale_t)0;
  locale_t locale = match_c_locale;
  if (*name && strcmp(name, "C") != 0 && strcmp(name, "POSIX") != 0) {
    locale = newlocale(LC_ALL_MASK, name, (locale_t)0);
    /* Like sudoers_setlocale, unavailable configured locales fall back to C;
     * an allocation failure is not an unavailable locale. */
    if (!locale) {
      if (errno == ENOMEM) return (locale_t)0;
      locale = match_c_locale;
    }
  }
  *previous = uselocale(locale);
  if (!*previous) {
    if (locale != match_c_locale) freelocale(locale);
    return (locale_t)0;
  }
  return locale;
}

static void match_locale_leave(locale_t locale, locale_t previous) {
  (void)uselocale(previous);
  if (locale != match_c_locale) freelocale(locale);
}

LEAN_EXPORT lean_obj_res leansudo_sys_regex(b_lean_obj_arg pattern, b_lean_obj_arg text,
    b_lean_obj_arg locale_name, lean_obj_arg world) {
  (void)world;
  regex_t re = {0};
  const char *expr = lean_string_cstr(pattern);
  size_t len = strlen(expr);
  if (len > 1024) return failure("regular expression too large");
  int flags = REG_EXTENDED | REG_NOSUB;
  const char *prefix = expr[0] == '^' ? expr + 1 : expr;
  char adjusted[1025];
  if (strncmp(prefix, "(?i)", 4) == 0) {
    flags |= REG_ICASE;
    if (expr[0] == '^') {
      memcpy(adjusted, expr + 4, len - 3);
      adjusted[0] = '^';
      expr = adjusted;
    } else {
      expr += 4;
    }
  }
  locale_t previous;
  locale_t locale = match_locale_enter(lean_string_cstr(locale_name), &previous);
  if (!locale) return failure("unable to initialize matching locale");
  int err = regex_check(expr);
  if (!err) err = regcomp(&re, expr, flags);
  if (err) {
    char msg[256];
    regerror(err, &re, msg, sizeof msg);
    match_locale_leave(locale, previous);
    return failure(msg);
  }
  err = regexec(&re, lean_string_cstr(text), 0, NULL, 0);
  regfree(&re);
  match_locale_leave(locale, previous);
  if (err != 0 && err != REG_NOMATCH) return failure("unable to match regular expression");
  return lean_io_result_mk_ok(lean_box(err == 0));
}
LEAN_EXPORT lean_obj_res leansudo_sys_glob(b_lean_obj_arg pattern,
    b_lean_obj_arg locale_name, lean_obj_arg world) {
  (void)world;
  locale_t previous;
  locale_t locale = match_locale_enter(lean_string_cstr(locale_name), &previous);
  if (!locale) return failure("unable to initialize matching locale");
  glob_t g = {0};
  int err = glob(lean_string_cstr(pattern), GLOB_NOSORT, NULL, &g);
  lean_object *out = lean_box(0);
  if (err == 0) {
    for (size_t n = g.gl_pathc; n > 0; n--) {
      lean_object *cell = lean_alloc_ctor(1, 2, 0);
      lean_ctor_set(cell, 0, lean_mk_string(g.gl_pathv[n - 1]));
      lean_ctor_set(cell, 1, out);
      out = cell;
    }
  }
  globfree(&g);
  match_locale_leave(locale, previous);
  if (err != 0 && err != GLOB_NOMATCH) return failure("unable to expand command glob");
  return lean_io_result_mk_ok(out);
}
LEAN_EXPORT lean_obj_res leansudo_sys_hostname(b_lean_obj_arg host, lean_obj_arg world) {
  (void)world;
  struct addrinfo hints = {0}, *res;
  hints.ai_flags = AI_CANONNAME;
  hints.ai_family = AF_UNSPEC;
  lean_object *out = lean_box(0);
  if (getaddrinfo(lean_string_cstr(host), NULL, &hints, &res) == 0) {
    if (res->ai_canonname) {
      out = lean_alloc_ctor(1, 1, 0);
      lean_ctor_set(out, 0, lean_mk_string(res->ai_canonname));
    }
    freeaddrinfo(res);
  }
  return lean_io_result_mk_ok(out);
}

/* Quote safe values and hex-encode unsafe bytes, as libaudit does. The caller
 * reserves 2*n+3 bytes, including quotes and termination. */
static void audit_value(char *out, const char *value, size_t n) {
  int encode = 0;
  for (size_t i = 0; i < n; i++) {
    unsigned char c = (unsigned char)value[i];
    if (c < 0x21 || c > 0x7e || c == '"') encode = 1;
  }
  static const char hex[] = "0123456789ABCDEF";
  if (encode) {
    for (size_t i = 0; i < n; i++) {
      unsigned char c = (unsigned char)value[i];
      *out++ = hex[c >> 4]; *out++ = hex[c & 15];
    }
  } else {
    *out++ = '"';
    memcpy(out, value, n); out += n;
    *out++ = '"';
  }
  *out = 0;
}

/* USER_CMD netlink record, matching audit_log_user_command's value encoding. */
LEAN_EXPORT lean_obj_res leansudo_sys_audit(b_lean_obj_arg command, b_lean_obj_arg tty, uint8_t success, lean_obj_arg world) {
  (void)world;
  int fd = socket(AF_NETLINK, SOCK_RAW | SOCK_CLOEXEC, NETLINK_AUDIT);
  if (fd < 0) return lean_io_result_mk_ok(lean_box(errno == EAFNOSUPPORT || errno == EPROTONOSUPPORT || errno == EINVAL));
  const char *cmd = lean_string_cstr(command);
  while (*cmd == ' ') cmd++;
  size_t n = strlen(cmd);
  while (n && (cmd[n - 1] == ' ' || cmd[n - 1] == '\n')) n--;
  if (n > 4095) n = 4095;
  char encoded_cmd[8193], encoded_cwd[8195], encoded_exe[8195], path[4096];
  audit_value(encoded_cmd, cmd, n);
  if (!getcwd(path, sizeof path)) strcpy(path, "?");
  audit_value(encoded_cwd, path, strlen(path));
  ssize_t plen = readlink("/proc/self/exe", path, sizeof path - 1);
  if (plen < 0) { path[0] = '?'; plen = 1; }
  path[plen] = 0;
  audit_value(encoded_exe, path, (size_t)plen);
  struct { struct nlmsghdr hdr; char data[8970]; } msg;
  memset(&msg, 0, sizeof msg);
  const char *term = lean_string_cstr(tty);
  /* Do not allow a terminal name to inject extra audit fields. */
  if (strpbrk(term, " \t\n\r\"'") != NULL) term = "(unknown)";
  if (strncmp(term, "/dev/", 5) == 0) term += 5;
  int len = snprintf(msg.data, sizeof msg.data, "cwd=%s cmd=%s exe=%s terminal=%s res=%s",
      encoded_cwd, encoded_cmd, encoded_exe, *term ? term : "?", success ? "success" : "failed");
  if (len < 0) { close(fd); return lean_io_result_mk_ok(lean_box(0)); }
  size_t used = strnlen(msg.data, sizeof msg.data - 1) + 1;
  msg.hdr.nlmsg_len = NLMSG_LENGTH(used);
  msg.hdr.nlmsg_type = AUDIT_USER_CMD;
  msg.hdr.nlmsg_flags = NLM_F_REQUEST | NLM_F_ACK;
  msg.hdr.nlmsg_seq = 1;
  struct sockaddr_nl kernel = {.nl_family = AF_NETLINK};
  int ok = sendto(fd, &msg, msg.hdr.nlmsg_len, 0, (struct sockaddr *)&kernel, sizeof kernel) >= 0;
  if (ok) {
    struct pollfd p = {.fd = fd, .events = POLLIN};
    if (poll(&p, 1, 1000) > 0) {
      union { struct nlmsghdr alignment; char bytes[4096]; } buf;
      struct sockaddr_nl sender = {0};
      socklen_t sender_len = sizeof sender;
      ssize_t got = recvfrom(fd, buf.bytes, sizeof buf.bytes, 0,
          (struct sockaddr *)&sender, &sender_len);
      if (got >= (ssize_t)NLMSG_LENGTH(sizeof(struct nlmsgerr)) && sender.nl_pid == 0) {
        struct nlmsghdr *h = (struct nlmsghdr *)buf.bytes;
        if (h->nlmsg_type == NLMSG_ERROR && h->nlmsg_seq == 1 &&
            h->nlmsg_len <= (unsigned)got && h->nlmsg_len >= NLMSG_LENGTH(sizeof(struct nlmsgerr))) {
          int e = ((struct nlmsgerr *)NLMSG_DATA(h))->error;
          ok = e == 0 || e == -ECONNREFUSED || e == -EPROTONOSUPPORT;
        } else ok = 0;
      } else ok = 0;
    } else ok = 0;
  } else if (errno == ECONNREFUSED || errno == EPROTONOSUPPORT) ok = 1;
  close(fd);
  return lean_io_result_mk_ok(lean_box(ok));
}
