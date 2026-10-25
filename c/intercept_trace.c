#ifndef _GNU_SOURCE
#define _GNU_SOURCE
#endif
#include "intercept.h"
#include "shim.h"
#include <errno.h>
#include <fcntl.h>
#include <limits.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <unistd.h>

#if defined(__linux__) && (defined(__x86_64__) || defined(__aarch64__))
#include <elf.h>
#include <linux/audit.h>
#include <linux/filter.h>
#include <linux/seccomp.h>
#include <stddef.h>
#include <sys/prctl.h>
#include <sys/ptrace.h>
#include <sys/syscall.h>
#include <sys/uio.h>
#if defined(__x86_64__)
#include <sys/user.h>
typedef struct user_regs_struct native_regs;
typedef struct {
  uint32_t ebx, ecx, edx, esi, edi, ebp, eax, ds, es, fs, gs;
  uint32_t orig_eax, eip, cs, eflags, esp, ss;
} compat_regs;
#define TRACE_ARCH AUDIT_ARCH_X86_64
#define TRACE_COMPAT_ARCH AUDIT_ARCH_I386
#define COMPAT_EXECVEAT 358
#define X32_EXECVE (0x40000000U + 520U)
#define X32_EXECVEAT (0x40000000U + 545U)
#else
#include <asm/ptrace.h>
typedef struct user_pt_regs native_regs;
typedef struct { uint32_t regs[18]; } compat_regs;
#define TRACE_ARCH AUDIT_ARCH_AARCH64
#define TRACE_COMPAT_ARCH AUDIT_ARCH_ARM
#define COMPAT_EXECVEAT 387
#ifndef NT_ARM_SYSTEM_CALL
#define NT_ARM_SYSTEM_CALL 0x404
#endif
#endif
enum { ABI_NATIVE, ABI_COMPAT, ABI_X32 };
typedef struct {
  union { native_regs native; compat_regs compat; } u;
  size_t bytes;
  unsigned abi;
  int compat_layout;
} trace_regs;

#define TRACE_BYTES (8U * 1024U * 1024U)
#define TRACE_STRING (2U * 1024U * 1024U)
struct trace_task {
  pid_t pid;
  int initial, newborn, denied, status;
  char **argv, **env;
  struct stat image;
  struct trace_task *next;
};
static struct trace_task *tasks;
static int gate[2] = {-1, -1};
static pid_t root_pid = -1;
static size_t page_size;

static void clear_expected(struct trace_task *t) {
  ls_strv_free(t->argv); ls_strv_free(t->env);
  t->argv = t->env = NULL;
}
static struct trace_task *task_find(pid_t pid) {
  for (struct trace_task *t = tasks; t; t = t->next)
    if (t->pid == pid) return t;
  return NULL;
}
static struct trace_task *task_add(pid_t pid) {
  struct trace_task *t = calloc(1, sizeof *t);
  if (t) { t->pid = pid; t->next = tasks; tasks = t; }
  return t;
}
static void task_remove(pid_t pid) {
  struct trace_task **p = &tasks;
  while (*p) {
    if ((*p)->pid == pid) {
      struct trace_task *t = *p;
      *p = t->next; clear_expected(t); free(t); return;
    }
    p = &(*p)->next;
  }
}
static struct trace_task *task_stopped(pid_t pid, int status) {
  struct trace_task *t = task_find(pid);
  unsigned event = (unsigned)status >> 16;
  if (event == PTRACE_EVENT_EXEC) {
    unsigned long oldpid = 0;
    if (ptrace(PTRACE_GETEVENTMSG, pid, NULL, &oldpid) < 0) return NULL;
    if (oldpid != (unsigned long)pid) {
      struct trace_task *old = task_find((pid_t)oldpid);
      if (!old) return NULL;
      task_remove(pid); old->pid = pid; t = old;
    }
  }
  if (!t) {
    if (event != PTRACE_EVENT_STOP) return NULL;
    t = task_add(pid);
    if (!t) return NULL;
    t->newborn = 1;
  }
  t->status = status;
  return t;
}
static int task_forked(pid_t pid) {
  unsigned long child = 0;
  if (ptrace(PTRACE_GETEVENTMSG, pid, NULL, &child) < 0 || !child || child > INT_MAX)
    return -1;
  if (!task_find((pid_t)child)) {
    struct trace_task *next = task_add((pid_t)child);
    if (!next) { kill((pid_t)child, SIGKILL); return -1; }
    next->newborn = 1;
  }
  return 0;
}
static int proc_path(char *out, size_t cap, pid_t pid, const char *name) {
  int n = snprintf(out, cap, "/proc/%ld/%s", (long)pid, name);
  if (n < 0 || (size_t)n >= cap) { errno = ENAMETOOLONG; return -1; }
  return 0;
}
static int proc_link(pid_t pid, const char *name, char *out, size_t cap) {
  char path[64];
  if (proc_path(path, sizeof path, pid, name)) return -1;
  ssize_t n = readlink(path, out, cap - 1);
  if (n < 0) return -1;
  if ((size_t)n == cap - 1) { errno = ENAMETOOLONG; return -1; }
  out[n] = 0; return 0;
}
static int remote_rw(pid_t pid, uintptr_t addr, void *data, size_t len, int writing) {
  if (!addr || addr > UINTPTR_MAX - len) { errno = EFAULT; return -1; }
  struct iovec local = {data, len}, remote = {(void *)addr, len};
  ssize_t done = writing ? process_vm_writev(pid, &local, 1, &remote, 1, 0) :
      process_vm_readv(pid, &local, 1, &remote, 1, 0);
  if (done == (ssize_t)len) return 0;
  size_t off = writing && done > 0 ? (size_t)done : 0;
  while (off < len) {
    uintptr_t pos = addr + off, aligned = pos & ~(uintptr_t)(sizeof(long) - 1);
    size_t skip = (size_t)(pos - aligned), n = sizeof(long) - skip;
    if (n > len - off) n = len - off;
    long word;
    if (!writing || skip || n != sizeof word) {
      errno = 0;
      word = ptrace(PTRACE_PEEKDATA, pid, (void *)aligned, NULL);
      if (errno) return -1;
    }
    if (writing) {
      memcpy((char *)&word + skip, (const char *)data + off, n);
      if (ptrace(PTRACE_POKEDATA, pid, (void *)aligned, (void *)(uintptr_t)word) < 0)
        return -1;
    } else {
      memcpy((char *)data + off, (char *)&word + skip, n);
    }
    off += n;
  }
  return 0;
}
static int remote_string_matches(pid_t pid, uintptr_t addr, const char *expected) {
  size_t len = strlen(expected) + 1;
  if (!addr || addr > UINTPTR_MAX - len) return 0;
  for (size_t off = 0; off < len;) {
    char buf[256];
    size_t n = len - off;
    if (n > sizeof buf) n = sizeof buf;
    if (remote_rw(pid, addr + off, buf, n, 0) || memcmp(buf, expected + off, n))
      return 0;
    off += n;
  }
  return 1;
}
static int remote_vector_matches(pid_t pid, uintptr_t addr, size_t width,
    char *const expected[]) {
  if (!addr) return expected[0] == NULL;
  for (size_t i = 0;; i++) {
    uintptr_t p;
    if (width == sizeof(uint32_t)) {
      uint32_t ptr32;
      if (remote_rw(pid, addr, &ptr32, sizeof ptr32, 0)) return 0;
      p = ptr32;
    } else if (remote_rw(pid, addr, &p, sizeof p, 0)) return 0;
    if (!expected[i]) return p == 0;
    if (!remote_string_matches(pid, p, expected[i]) || addr > UINTPTR_MAX - width)
      return 0;
    addr += width;
  }
}
static char *remote_string(pid_t pid, uintptr_t addr, size_t *budget) {
  char *s = NULL;
  size_t used = 0, cap = 0;
  while (used < TRACE_STRING && *budget) {
    char buf[256];
    size_t n = sizeof buf, boundary = page_size - (addr % page_size);
    if (n > boundary) n = boundary;
    if (n > *budget) n = *budget;
    if (remote_rw(pid, addr, buf, n, 0)) break;
    char *end = memchr(buf, 0, n);
    if (end) n = (size_t)(end - buf) + 1;
    if (used + n > cap) {
      size_t next = cap ? cap * 2 : 256;
      char *p = realloc(s, next);
      if (!p) break;
      s = p; cap = next;
    }
    memcpy(s + used, buf, n); used += n; *budget -= n;
    if (end) return s;
    if (addr > UINTPTR_MAX - n) break;
    addr += n;
  }
  free(s); errno = EFAULT; return NULL;
}
static char **remote_vector(pid_t pid, uintptr_t addr, size_t width, size_t *budget) {
  size_t count = 0, cap = 16;
  char **v = calloc(cap, sizeof *v);
  if (!v) return NULL;
  if (!addr) return v;
  while (*budget >= width) {
    uintptr_t p;
    if (width == sizeof(uint32_t)) {
      uint32_t ptr32;
      if (remote_rw(pid, addr, &ptr32, sizeof ptr32, 0)) break;
      p = ptr32;
    } else if (remote_rw(pid, addr, &p, sizeof p, 0)) break;
    *budget -= width;
    if (!p) return v;
    if (count + 1 == cap) {
      size_t next = cap * 2;
      char **nv = realloc(v, next * sizeof *v);
      if (!nv) break;
      v = nv; cap = next;
    }
    v[count] = remote_string(pid, p, budget);
    if (!v[count]) break;
    v[++count] = NULL;
    if (addr > UINTPTR_MAX - width) break;
    addr += width;
  }
  ls_strv_free(v); errno = EFAULT; return NULL;
}
static int get_regs(pid_t pid, trace_regs *r) {
  struct iovec iov = {&r->u, sizeof r->u};
  if (ptrace(PTRACE_GETREGSET, pid, (void *)(uintptr_t)NT_PRSTATUS, &iov) < 0)
    return -1;
  if (iov.iov_len != sizeof(native_regs) && iov.iov_len != sizeof(compat_regs)) {
    errno = ENOTSUP; return -1;
  }
  r->bytes = iov.iov_len;
  r->compat_layout = iov.iov_len == sizeof(compat_regs);
  r->abi = r->compat_layout ? ABI_COMPAT : ABI_NATIVE;
  return 0;
}
static int put_regs(pid_t pid, trace_regs *r) {
  struct iovec iov = {&r->u, r->bytes};
  return ptrace(PTRACE_SETREGSET, pid, (void *)(uintptr_t)NT_PRSTATUS, &iov) < 0 ? -1 : 0;
}
static uintptr_t reg_arg(const trace_regs *r, unsigned n) {
#if defined(__x86_64__)
  uintptr_t value;
  if (r->compat_layout) {
    switch (n) {
    case 0: return r->u.compat.ebx; case 1: return r->u.compat.ecx;
    default: return r->u.compat.edx;
    }
  }
  if (r->abi == ABI_COMPAT) {
    switch (n) {
    case 0: value = r->u.native.rbx; break;
    case 1: value = r->u.native.rcx; break;
    default: value = r->u.native.rdx; break;
    }
  } else {
    switch (n) {
    case 0: value = r->u.native.rdi; break;
    case 1: value = r->u.native.rsi; break;
    default: value = r->u.native.rdx; break;
    }
  }
  return r->abi == ABI_COMPAT ? (uint32_t)value : value;
#else
  return r->compat_layout ? r->u.compat.regs[n] : r->u.native.regs[n];
#endif
}
static void set_reg_arg(trace_regs *r, unsigned n, uintptr_t value) {
#if defined(__x86_64__)
  if (r->compat_layout) {
    switch (n) {
    case 0: r->u.compat.ebx = (uint32_t)value; break;
    case 1: r->u.compat.ecx = (uint32_t)value; break;
    default: r->u.compat.edx = (uint32_t)value; break;
    }
  } else if (r->abi == ABI_COMPAT) {
    switch (n) {
    case 0: r->u.native.rbx = (uint32_t)value; break;
    case 1: r->u.native.rcx = (uint32_t)value; break;
    default: r->u.native.rdx = (uint32_t)value; break;
    }
  } else {
    switch (n) {
    case 0: r->u.native.rdi = value; break;
    case 1: r->u.native.rsi = value; break;
    default: r->u.native.rdx = value; break;
    }
  }
#else
  if (r->compat_layout) r->u.compat.regs[n] = (uint32_t)value;
  else r->u.native.regs[n] = value;
#endif
}
static uintptr_t reg_sp(const trace_regs *r) {
#if defined(__x86_64__)
  return r->compat_layout ? r->u.compat.esp : r->u.native.rsp;
#else
  return r->compat_layout ? r->u.compat.regs[13] : r->u.native.sp;
#endif
}
static long reg_syscall(const trace_regs *r) {
#if defined(__x86_64__)
  unsigned long nr = r->compat_layout ? r->u.compat.orig_eax : r->u.native.orig_rax;
  if (r->abi == ABI_X32) {
    if (nr == X32_EXECVE) return SYS_execve;
    if (nr == X32_EXECVEAT) return SYS_execveat;
    return -1;
  }
#else
  unsigned long nr = r->compat_layout ? r->u.compat.regs[7] : r->u.native.regs[8];
#endif
  if (r->abi == ABI_COMPAT) {
    if (nr == 11) return SYS_execve;
    if (nr == COMPAT_EXECVEAT) return SYS_execveat;
    return -1;
  }
  return (long)nr;
}
static int skip_exec(pid_t pid, trace_regs *r) {
#if defined(__x86_64__)
  if (r->compat_layout) r->u.compat.orig_eax = UINT32_MAX;
  else r->u.native.orig_rax = (unsigned long)-1;
  return put_regs(pid, r);
#else
  if (r->compat_layout) r->u.compat.regs[0] = (uint32_t)-ENOSYS;
  else r->u.native.regs[0] = (unsigned long)-ENOSYS;
  if (put_regs(pid, r)) return -1;
  int nr = -1;
  struct iovec iov = {&nr, sizeof nr};
  return ptrace(PTRACE_SETREGSET, pid, (void *)(uintptr_t)NT_ARM_SYSTEM_CALL, &iov) < 0
      ? -1 : 0;
#endif
}
static int deny_exec(struct trace_task *t, trace_regs *r) {
  if (skip_exec(t->pid, r)) return -1;
  t->denied = 1;
  if (ptrace(PTRACE_SYSCALL, t->pid, NULL, NULL) < 0) return -1;
  t->status = 0;
  return 0;
}
static int denied_exit(struct trace_task *t) {
  trace_regs r;
  if (get_regs(t->pid, &r)) return -1;
#if defined(__x86_64__)
  if (r.compat_layout) r.u.compat.eax = (uint32_t)-EACCES;
  else r.u.native.rax = (unsigned long)-EACCES;
#else
  if (r.compat_layout) r.u.compat.regs[0] = (uint32_t)-EACCES;
  else r.u.native.regs[0] = (unsigned long)-EACCES;
#endif
  if (put_regs(t->pid, &r)) return -1;
  t->denied = 0; return 0;
}
static int syscall_stat(pid_t pid, const char *raw, struct stat *st) {
  char path[PATH_MAX + 64];
  int n;
  if (raw[0] == '/') {
    n = snprintf(path, sizeof path, "/proc/%ld/root%s", (long)pid, raw);
  } else {
    n = snprintf(path, sizeof path, "/proc/%ld/cwd/%s", (long)pid, raw);
  }
  if (n < 0 || (size_t)n >= sizeof path) { errno = ENAMETOOLONG; return -1; }
  return stat(path, st);
}
static char *exec_path(const char *raw, const char *cwd) {
  if (!*raw) return NULL;
  if (raw[0] == '/') return strdup(raw);
  char joined[PATH_MAX], parent[PATH_MAX], *path = NULL;
  int n = snprintf(joined, sizeof joined, "%s/%s", cwd, raw);
  if (n < 0 || (size_t)n >= sizeof joined) return NULL;
  char *base = strrchr(joined, '/');
  if (!base) return NULL;
  *base++ = '\0';
  if (!realpath(*joined ? joined : "/", parent)) return NULL;
  if (asprintf(&path, "%s%s%s", parent, strcmp(parent, "/") ? "/" : "", base) < 0)
    return NULL;
  return path;
}
static int expected_image(const char *command, const char *label,
    const char *cwd, char ***argv, struct stat *image, const struct stat *requested) {
  char *current = strdup(command);
  if (!current) return -1;
  int result = -1;
  for (unsigned depth = 0; depth <= 4; depth++) {
    char header[256];
    int fd = open(current, O_RDONLY | O_CLOEXEC);
    if (fd < 0) break;
    ssize_t n;
    n = TEMP_FAILURE_RETRY(read(fd, header, sizeof header));
    int ok = fstat(fd, image); close(fd);
    if (n < 0 || ok || !S_ISREG(image->st_mode)) break;
    if (!depth && (image->st_dev != requested->st_dev || image->st_ino != requested->st_ino))
      break;
    if (n < 2 || header[0] != '#' || header[1] != '!') { result = 0; break; }
    if (depth == 4) break;
    char *end = memchr(header, '\n', (size_t)n);
    if (!end) {
      if (n == (ssize_t)sizeof header) break;
      end = header + n;
    }
    while (end > header + 2 && (end[-1] == ' ' || end[-1] == '\t')) end--;
    *end = 0;
    char *interp = header + 2;
    while (*interp == ' ' || *interp == '\t') interp++;
    char *opt = interp;
    while (*opt && *opt != ' ' && *opt != '\t') opt++;
    if (*opt) {
      *opt++ = 0;
      while (*opt == ' ' || *opt == '\t') opt++;
    }
    if (!*interp) break;
    size_t count = 0;
    while ((*argv)[count]) count++;
    size_t prefix = *opt ? 3 : 2;
    char **next = calloc(count + prefix + 1, sizeof *next);
    char *newpath = NULL;
    if (interp[0] == '/') newpath = strdup(interp);
    else if (asprintf(&newpath, "%s/%s", cwd, interp) < 0) newpath = NULL;
    if (!next || !newpath) { free(next); free(newpath); break; }
    next[0] = strdup(interp);
    if (*opt) next[1] = strdup(opt);
    next[prefix - 1] = strdup(label);
    if (!next[0] || (*opt && !next[1]) || !next[prefix - 1]) {
      for (size_t i = 0; i < prefix; i++) free(next[i]);
      free(next); free(newpath); break;
    }
    for (size_t i = 1; i < count; i++) next[prefix + i - 1] = (*argv)[i];
    free((*argv)[0]); free(*argv); *argv = next;
    label = next[0];
    free(current); current = newpath;
  }
  free(current); return result;
}
static int proc_vector_matches(pid_t pid, const char *name, char *const expected[]) {
  char path[64], buf[4096];
  if (proc_path(path, sizeof path, pid, name)) return 0;
  int fd = open(path, O_RDONLY | O_CLOEXEC);
  if (fd < 0) return 0;
  size_t index = 0, off = 0;
  int match = 1;
  for (;;) {
    ssize_t n = read(fd, buf, sizeof buf);
    if (n < 0 && errno == EINTR) continue;
    if (n < 0) { match = 0; break; }
    if (!n) break;
    for (ssize_t i = 0; i < n; i++) {
      if (!expected[index] || buf[i] != expected[index][off]) { match = 0; break; }
      if (!buf[i]) { index++; off = 0; } else off++;
    }
    if (!match) break;
  }
  close(fd);
  return match && !off && !expected[index];
}
static int verify_exec(struct trace_task *t) {
  char path[64]; struct stat st;
  if (proc_path(path, sizeof path, t->pid, "exe") || stat(path, &st) ||
      st.st_dev != t->image.st_dev || st.st_ino != t->image.st_ino) return -1;
  return proc_vector_matches(t->pid, "cmdline", t->argv) &&
      proc_vector_matches(t->pid, "environ", t->env) ? 0 : -1;
}
static int rewrite_path(pid_t pid, trace_regs *r, const char *command,
    char *const argv[], char *const env[], int empty_argv) {
  size_t len = strlen(command) + 1;
  size_t space = (len + sizeof(long) - 1) & ~(sizeof(long) - 1);
  uintptr_t sp = reg_sp(r);
  if (sp < 128 || sp - 128 < space) return -1;
  uintptr_t addr = sp - 128 - space;
  if (r->abi == ABI_COMPAT && addr > UINT32_MAX) return -1;
  if (remote_rw(pid, addr, (void *)command, len, 1)) return -1;
  set_reg_arg(r, 0, addr);
  if (put_regs(pid, r)) return -1;

  trace_regs actual;
  if (get_regs(pid, &actual) || actual.compat_layout != r->compat_layout) return -1;
  actual.abi = r->abi;
  if (reg_syscall(&actual) != SYS_execve || reg_arg(&actual, 0) != addr ||
      reg_arg(&actual, 1) != reg_arg(r, 1) || reg_arg(&actual, 2) != reg_arg(r, 2))
    return -1;
  size_t width = r->abi == ABI_NATIVE ? sizeof(uintptr_t) : sizeof(uint32_t);
  char *empty[] = {NULL};
  return remote_string_matches(pid, addr, command) &&
      remote_vector_matches(pid, reg_arg(&actual, 1), width, empty_argv ? empty : argv) &&
      remote_vector_matches(pid, reg_arg(&actual, 2), width, env) ? 0 : -1;
}
static int check_exec(struct trace_task *t) {
  trace_regs r;
  if (get_regs(t->pid, &r)) return -1;
  unsigned long abi;
  if (ptrace(PTRACE_GETEVENTMSG, t->pid, NULL, &abi) < 0 || abi > ABI_X32 ||
      (r.compat_layout && abi != ABI_COMPAT)) return -1;
#if defined(__aarch64__)
  if ((abi == ABI_COMPAT) != r.compat_layout || abi == ABI_X32) return -1;
#endif
  r.abi = (unsigned)abi;
  long nr = reg_syscall(&r);
  if (nr != SYS_execve && nr != SYS_execveat) return -1;
  clear_expected(t);
  if (t->initial) { t->initial = 0; return 0; }
  if (nr == SYS_execveat) return 0;
  size_t budget = TRACE_BYTES;
  char *raw = remote_string(t->pid, reg_arg(&r, 0), &budget);
  size_t width = r.abi == ABI_NATIVE ? sizeof(uintptr_t) : sizeof(uint32_t);
  char **argv = remote_vector(t->pid, reg_arg(&r, 1), width, &budget);
  char **env = remote_vector(t->pid, reg_arg(&r, 2), width, &budget);
  int empty_argv = argv && !argv[0];
  if (empty_argv) {
    argv[0] = strdup("");
  }
  char cwd[PATH_MAX];
  char *command = NULL;
  struct stat st, expected;
  int allow = 0;
  if (raw && argv && argv[0] && env && !proc_link(t->pid, "cwd", cwd, sizeof cwd) &&
      cwd[0] == '/') command = exec_path(raw, cwd);
  int verify = ls_intercept_verify();
  if (command && !syscall_stat(t->pid, raw, &st) &&
      (!verify || !stat(command, &expected))) {
    int setid = (st.st_mode & (S_ISUID | S_ISGID)) != 0;
    allow = ls_intercept_check(command, argv, env, cwd, t->pid, setid) == 1;
    if (allow && raw[0] != '/' && rewrite_path(t->pid, &r, command, argv, env, empty_argv))
      allow = 0;
    if (allow && verify) {
      if (expected_image(command, raw, cwd, &argv, &t->image, &expected))
        allow = 0;
      else { t->argv = argv; t->env = env; argv = env = NULL; }
    }
  }
  free(raw); free(command); ls_strv_free(argv); ls_strv_free(env);
  if (!allow) return deny_exec(t, &r) ? -1 : 1;
  return 0;
}

int ls_intercept_trace_supported(void) {
  return ls_trace_supported();
}

int ls_intercept_trace_prepare(void) {
  if (!ls_intercept_trace()) return 0;
  if (gate[0] >= 0 || tasks) { errno = EBUSY; return -1; }
  long page = sysconf(_SC_PAGESIZE);
  if (page <= 0) { errno = EINVAL; return -1; }
  page_size = (size_t)page;
  return pipe2(gate, O_CLOEXEC);
}
int ls_intercept_trace_child(void) {
  if (!ls_intercept_trace()) return 0;
  if (gate[0] < 0 || gate[1] < 0) { errno = EINVAL; return -1; }
  close(gate[1]); gate[1] = -1;
  char ready = 0; ssize_t n;
  n = TEMP_FAILURE_RETRY(read(gate[0], &ready, 1));
  close(gate[0]); gate[0] = -1;
  if (n != 1 || ready != 1) { errno = EACCES; return -1; }
  struct sock_filter filter[] = {
    BPF_STMT(BPF_LD | BPF_W | BPF_ABS, offsetof(struct seccomp_data, arch)),
    BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, TRACE_COMPAT_ARCH, 0, 5),
    BPF_STMT(BPF_LD | BPF_W | BPF_ABS, offsetof(struct seccomp_data, nr)),
    BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, 11, 1, 0),
    BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, COMPAT_EXECVEAT, 0, 1),
    BPF_STMT(BPF_RET | BPF_K, SECCOMP_RET_TRACE | ABI_COMPAT),
    BPF_STMT(BPF_RET | BPF_K, SECCOMP_RET_ALLOW),
    BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, TRACE_ARCH, 1, 0),
    BPF_STMT(BPF_RET | BPF_K, SECCOMP_RET_KILL_PROCESS),
    BPF_STMT(BPF_LD | BPF_W | BPF_ABS, offsetof(struct seccomp_data, nr)),
#if defined(__x86_64__)
    BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, X32_EXECVE, 1, 0),
    BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, X32_EXECVEAT, 0, 1),
    BPF_STMT(BPF_RET | BPF_K, SECCOMP_RET_TRACE | ABI_X32),
#endif
    BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, SYS_execve, 1, 0),
    BPF_JUMP(BPF_JMP | BPF_JEQ | BPF_K, SYS_execveat, 0, 1),
    BPF_STMT(BPF_RET | BPF_K, SECCOMP_RET_TRACE),
    BPF_STMT(BPF_RET | BPF_K, SECCOMP_RET_ALLOW)
  };
  struct sock_fprog prog = {(unsigned short)(sizeof filter / sizeof filter[0]), filter};
  return prctl(PR_SET_SECCOMP, SECCOMP_MODE_FILTER, &prog);
}
int ls_intercept_trace_attach(pid_t pid) {
  if (!ls_intercept_trace()) return 0;
  if (gate[0] < 0 || gate[1] < 0 || pid <= 0) { errno = EINVAL; return -1; }
  struct trace_task *t = task_add(pid);
  if (!t) return -1;
  t->initial = 1; root_pid = pid;
  unsigned long options = PTRACE_O_TRACESECCOMP | PTRACE_O_TRACEEXEC |
      PTRACE_O_TRACEFORK | PTRACE_O_TRACEVFORK | PTRACE_O_TRACECLONE |
      PTRACE_O_TRACESYSGOOD;
  if (ptrace(PTRACE_SEIZE, pid, NULL, (void *)options) < 0) {
    task_remove(pid); kill(pid, SIGKILL); return -1;
  }
  close(gate[0]); gate[0] = -1;
  char ready = 1; ssize_t n;
  n = TEMP_FAILURE_RETRY(write(gate[1], &ready, 1));
  close(gate[1]); gate[1] = -1;
  if (n != 1) { kill(pid, SIGKILL); return -1; }
  return 0;
}
int ls_intercept_trace_wait(pid_t pid, int status) {
  if (!ls_intercept_trace()) return 0;
  if (pid == ls_intercept_broker_pid()) return 1;
  struct trace_task *t = task_find(pid);
  if (WIFEXITED(status) || WIFSIGNALED(status)) {
    task_remove(pid); return pid == root_pid ? 0 : 1;
  }
  if (!WIFSTOPPED(status)) return pid == root_pid ? 0 : 1;
  unsigned event = (unsigned)status >> 16;
  int sig = WSTOPSIG(status), deliver = 0;
  if (!t && !event) return 1;
  t = task_stopped(pid, status);
  if (!t) goto fail;
  if (event == PTRACE_EVENT_SECCOMP) {
    int result = check_exec(t);
    if (result < 0) goto fail;
    if (result > 0) return 1;
  } else if (event == PTRACE_EVENT_EXEC) {
    if (t->argv && verify_exec(t)) {
      kill(pid, SIGKILL);
      (void)ptrace(PTRACE_CONT, pid, NULL, (void *)(intptr_t)SIGKILL);
      t->status = 0;
      clear_expected(t);
      return 1;
    }
    clear_expected(t);
  } else if (event == PTRACE_EVENT_FORK || event == PTRACE_EVENT_VFORK || event == PTRACE_EVENT_CLONE) {
    if (task_forked(pid)) goto fail;
  } else if (sig == (SIGTRAP | 0x80) && t->denied) {
    if (denied_exit(t)) goto fail;
  } else if (event == PTRACE_EVENT_STOP) {
    if (t->newborn) t->newborn = 0;
    else if (sig == SIGSTOP || sig == SIGTSTP || sig == SIGTTIN || sig == SIGTTOU) {
      if (ptrace(PTRACE_LISTEN, pid, NULL, NULL) < 0) goto fail;
      t->status = 0;
      return pid == root_pid ? 0 : 1;
    }
  } else if (!event) {
    deliver = sig;
  } else goto fail;
  if (ptrace(t->denied ? PTRACE_SYSCALL : PTRACE_CONT, pid, NULL, (void *)(intptr_t)deliver) < 0) {
    if (errno != ESRCH) goto fail;
  }
  t->status = 0;
  return 1;
fail:
  kill(pid, SIGKILL); errno = EACCES; return -1;
}
void ls_intercept_trace_close(void) {
  for (unsigned i = 0; i < 2; i++) {
    if (gate[i] >= 0) close(gate[i]);
    gate[i] = -1;
  }
  for (struct trace_task *t = tasks; t; t = t->next) {
    if (!t->status && ptrace(PTRACE_INTERRUPT, t->pid, NULL, NULL) < 0 && errno != ESRCH)
      kill(t->pid, SIGKILL);
  }
  while (tasks) {
    struct trace_task *t;
    for (t = tasks; t && !t->status; t = t->next) { }
    if (!t) {
      int status;
      pid_t pid = waitpid(-1, &status, __WALL);
      if (pid < 0) {
        if (errno == EINTR) continue;
        int wait_error = errno;
        while (tasks) {
          if (wait_error != ECHILD) kill(tasks->pid, SIGKILL);
          task_remove(tasks->pid);
        }
        break;
      }
      if (pid == ls_intercept_broker_pid()) continue;
      if (WIFEXITED(status) || WIFSIGNALED(status)) { task_remove(pid); continue; }
      if (!WIFSTOPPED(status)) continue;
      if (!task_find(pid) && !((unsigned)status >> 16)) continue;
      t = task_stopped(pid, status);
      if (!t) { kill(pid, SIGKILL); continue; }
    }
    pid_t pid = t->pid;
    unsigned event = (unsigned)t->status >> 16;
    int sig = WSTOPSIG(t->status), deliver = 0, failed = 0;
    if (event == PTRACE_EVENT_SECCOMP) {
      trace_regs r;
      failed = get_regs(pid, &r) || skip_exec(pid, &r);
    } else if (event == PTRACE_EVENT_EXEC) {
      failed = t->argv && verify_exec(t);
    } else if (event == PTRACE_EVENT_FORK || event == PTRACE_EVENT_VFORK ||
        event == PTRACE_EVENT_CLONE) {
      failed = task_forked(pid);
    } else if (!event && sig == (SIGTRAP | 0x80)) {
      failed = !t->denied || denied_exit(t);
    } else if (!event) {
      deliver = sig;
    } else if (event != PTRACE_EVENT_STOP) {
      failed = 1;
    }
    if (failed) kill(pid, SIGKILL);
    if (ptrace(PTRACE_DETACH, pid, NULL,
        (void *)(intptr_t)(failed ? SIGKILL : deliver)) < 0 && errno != ESRCH)
      kill(pid, SIGKILL);
    task_remove(pid);
  }
  root_pid = -1;
}
#else
int ls_intercept_trace_prepare(void) { if (!ls_intercept_trace()) return 0; errno = ENOTSUP; return -1; }
int ls_intercept_trace_child(void) { if (!ls_intercept_trace()) return 0; errno = ENOTSUP; return -1; }
int ls_intercept_trace_attach(pid_t pid) { (void)pid; if (!ls_intercept_trace()) return 0; errno = ENOTSUP; return -1; }
int ls_intercept_trace_wait(pid_t pid, int status) { (void)pid; (void)status; if (!ls_intercept_trace()) return 0; errno = ENOTSUP; return -1; }
void ls_intercept_trace_close(void) { }
int ls_intercept_trace_supported(void) { return 0; }
#endif
