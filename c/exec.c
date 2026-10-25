/*
 * Job-control and tty-size handling follows sudo's suspend_parent.c and
 * ttysize.c. Copyright (c) 2009-2023 Todd C. Miller <Todd.Miller@sudo.ws>.
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
/*
 * c/exec.c — command execution for lean-sudo (owned by LeanSudo/Sys/Exec.lean).
 *
 * Responsibilities: fork, privilege drop (with verification), execve, signal relay,
 * wait, job-control (stop/continue) propagation, and the optional pty mode.
 * No policy lives here: every decision about *what* to run with *which* ids has
 * already been made by the verified Lean core; this file only carries it out and
 * fails closed (the child `_exit(127)`s without exec'ing) if any step does not take.
 *
 * Process structure
 *   non-pty:   sudo ── command                (command shares sudo's pgrp/session)
 *   pty:       sudo ── monitor ── command     (monitor = session leader of the pty,
 *                                             command = own pgrp in that session)
 *   The monitor exists so that the command's process group is not orphaned (a
 *   process group whose parent is in another session would ignore terminal stop
 *   signals) and so that job-control events can be relayed back to sudo.
 *
 * Invariants
 *   - Everything that runs after fork() in a child is async-signal-safe: all memory
 *     the child needs (argv/envp arrays, group buffers) is allocated before fork.
 *   - The child resets signal dispositions/mask to the state recorded at process start
 *     (before the Lean runtime initialised), then: setgroups → setresgid → setresuid →
 *     verify (getres[ug]id, getgroups, setuid(0) must fail unless a requested ID is 0) →
 *     chdir → umask →
 *     mark fds >= closefrom close-on-exec → execve.
 *   - Any failure in the child is reported through a CLOEXEC pipe as (errno, stage);
 *     EOF on that pipe means execve succeeded.
 *   - The parent's signal handlers only write a record to a non-blocking self-pipe;
 *     all decisions are taken in the main loop.
 *   - In pty mode the user's terminal is always restored before sudo stops itself and
 *     before runCommand returns.
 */
#include <lean/lean.h>
#include "intercept.h"
#include "intercept_dso.h"
#include "logsrv.h"

#include <errno.h>
#include <fcntl.h>
#include <grp.h>
#include <poll.h>
#include <pty.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/ioctl.h>
#include <sys/resource.h>
#include <sys/socket.h>
#include <sys/prctl.h>
#include <time.h>
#include <utmpx.h>
#include <sys/syscall.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <sys/uio.h>
#include <sys/wait.h>
#include <termios.h>
#include <unistd.h>

extern int ls_iolog_active(void);
extern int ls_iolog_stream(int);
extern int ls_iolog_write(int, const void *, size_t);
extern int ls_iolog_winsize(unsigned, unsigned);
extern int ls_iolog_suspend(int);
extern int ls_iolog_close(int, int);
extern void ls_iolog_child_close(void);
extern int lean_sudo_initialize_locale(void);

struct io_channel {
  int parent, child, enabled;
  char pending[8192];
  size_t off, len;
};
static struct io_channel io_channels[3];

static void io_channels_close(void) {
  for (int i = 0; i < 3; i++) {
    if (io_channels[i].parent >= 0) close(io_channels[i].parent);
    if (io_channels[i].child >= 0) close(io_channels[i].child);
    io_channels[i].parent = io_channels[i].child = -1;
  }
}

static int io_channels_open(int ttymask) {
  for (int i = 0; i < 3; i++) {
    memset(&io_channels[i], 0, sizeof io_channels[i]);
    io_channels[i].parent = io_channels[i].child = -1;
  }
  for (int i = 0; i < 3; i++) {
    if ((ttymask & (1 << i)) || !ls_iolog_stream(i)) continue;
    int fds[2];
    if (pipe2(fds, O_CLOEXEC)) { io_channels_close(); return -1; }
    io_channels[i].parent = fds[i == 0 ? 1 : 0];
    io_channels[i].child = fds[i == 0 ? 0 : 1];
    io_channels[i].enabled = 1;
    if (fcntl(io_channels[i].parent, F_SETFL, O_NONBLOCK)) {
      io_channels_close(); return -1;
    }
  }
  return 0;
}

static void io_channel_poll(struct pollfd *p) {
  for (int i = 0; i < 3; i++) {
    struct io_channel *c = &io_channels[i];
    int fd = c->parent;
    short events = POLLIN;
    if (i == 0 && fd >= 0) {
      if (c->len) events = POLLOUT;
      else fd = STDIN_FILENO;
    }
    p[i] = (struct pollfd){.fd = fd, .events = events};
  }
}

static int io_channel_pump(struct pollfd *p) {
  for (int i = 0; i < 3; i++) {
    struct io_channel *c = &io_channels[i];
    if (c->parent < 0 || !p[i].revents) continue;
    if (i == 0 && c->len) {
      ssize_t n = write(c->parent, c->pending + c->off, c->len - c->off);
      if (n > 0) {
        c->off += (size_t)n;
        if (c->off == c->len) c->off = c->len = 0;
      } else if (n < 0 && errno != EINTR && errno != EAGAIN) {
        close(c->parent); c->parent = -1;
      }
      continue;
    }
    ssize_t n = read(i == 0 ? STDIN_FILENO : c->parent, c->pending, sizeof c->pending);
    if (n > 0) {
      if (ls_iolog_write(i, c->pending, (size_t)n)) return -1;
      if (i == 0) { c->len = (size_t)n; c->off = 0; }
      else {
        size_t off = 0;
        while (off < (size_t)n) {
          ssize_t written = write(i, c->pending + off, (size_t)n - off);
          if (written < 0 && errno == EINTR) continue;
          if (written <= 0) break;
          off += (size_t)written;
        }
      }
    } else if (!n || (errno != EINTR && errno != EAGAIN)) {
      close(c->parent); c->parent = -1;
    }
  }
  return 0;
}

static int io_channels_drain(void) {
  if (io_channels[0].parent >= 0) {
    close(io_channels[0].parent); io_channels[0].parent = -1;
  }
  while (io_channels[1].parent >= 0 || io_channels[2].parent >= 0) {
    struct pollfd p[3];
    io_channel_poll(p);
    int n = poll(p, 3, 100);
    if (n < 0 && errno == EINTR) continue;
    if (n <= 0) break;
    if (io_channel_pump(p)) return -1;
  }
  return 0;
}

#ifndef CLOSE_RANGE_CLOEXEC
#define CLOSE_RANGE_CLOEXEC (1U << 2)
#endif

/* ------------------------------------------------------------------------- */
/* Startup signal state (like sudo's save_signals/restore_signals).           */
/* ------------------------------------------------------------------------- */

/* Recorded by a constructor, i.e. before the Lean runtime starts, so that the
 * command inherits the dispositions sudo itself was started with (in particular
 * an ignored/default SIGPIPE) rather than whatever the runtime changed. */
static unsigned char g_startup_ignored[NSIG];
static sigset_t g_startup_mask;
/* stay_setuid retains the invoking real IDs, even if PAM changes credentials. */
static uid_t g_invoking_uid;
static gid_t g_invoking_gid;
static struct rlimit g_core_limit;
static int g_core_saved;
static int g_dumpable = -1;
static struct rlimit g_user_limits[RLIM_NLIMITS];
static unsigned char g_user_limit_saved[RLIM_NLIMITS];

__attribute__((constructor)) static void leansudo_exec_save_signals(void) {
  struct sigaction sa;
  g_invoking_uid = getuid();
  g_invoking_gid = getgid();
  for (int i = 0; i < RLIM_NLIMITS; i++)
    g_user_limit_saved[i] = getrlimit(i, &g_user_limits[i]) == 0;
  for (int sig = 1; sig < NSIG; sig++) {
    if (sigaction(sig, NULL, &sa) == 0)
      g_startup_ignored[sig] = (sa.sa_handler == SIG_IGN);
  }
  if (sigprocmask(SIG_SETMASK, NULL, &g_startup_mask) != 0)
    sigemptyset(&g_startup_mask);
}

/* Async-signal-safe. Errors for signals that cannot be changed (SIGKILL, SIGSTOP,
 * libc-internal real-time signals) are expected and ignored. */
static int restore_startup_signals(void) {
  struct sigaction sa;
  memset(&sa, 0, sizeof sa);
  sigemptyset(&sa.sa_mask);
  for (int sig = 1; sig < NSIG; sig++) {
    if (sig == SIGKILL || sig == SIGSTOP)
      continue;
    sa.sa_handler = g_startup_ignored[sig] ? SIG_IGN : SIG_DFL;
    (void)sigaction(sig, &sa, NULL);
  }
  return sigprocmask(SIG_SETMASK, &g_startup_mask, NULL);
}

/* ------------------------------------------------------------------------- */
/* Self-pipe signal relay.                                                    */
/* ------------------------------------------------------------------------- */

struct sigrec {
  int signo;
  int code;    /* si_code */
  pid_t pid;   /* si_pid (meaningful for user-sent signals and SIGCHLD) */
  pid_t pgrp;  /* sender's process group, -1 if unknown / not user-sent */
  pid_t sid;   /* sender's session, -1 if unknown / not user-sent */
};

static volatile sig_atomic_t g_sigpipe_wr = -1;

static void relay_handler(int signo, siginfo_t *si, void *uctx) {
  (void)uctx;
  int saved = errno;
  struct sigrec r;
  r.signo = signo;
  r.code = si ? si->si_code : 0;
  r.pid = si ? si->si_pid : 0;
  r.pgrp = r.sid = -1;
  if (r.code <= 0 && r.pid > 0) {
    /* Look the sender up now, while it most likely still exists (a `kill`
     * process exits right after sending); getpgid/getsid are plain syscalls. */
    r.pgrp = getpgid(r.pid);
    r.sid = getsid(r.pid);
  }
  int fd = g_sigpipe_wr;
  if (fd >= 0) {
    /* sizeof r < PIPE_BUF: atomic; if the pipe is full the record is dropped. */
    ssize_t n = write(fd, &r, sizeof r);
    (void)n;
  }
  errno = saved;
}

/* Signals whose handlers we install in the parent. */
static const int k_relay_sigs[] = {SIGINT,  SIGQUIT, SIGTSTP, SIGTERM, SIGHUP,  SIGALRM,
                                   SIGUSR1, SIGUSR2, SIGPIPE, SIGCHLD, SIGCONT, SIGWINCH};
#define N_RELAY_SIGS (sizeof k_relay_sigs / sizeof k_relay_sigs[0])

struct sigstate {
  int pipe_rd, pipe_wr;
  struct sigaction old[N_RELAY_SIGS];
  struct sigaction old_ttin, old_ttou;
  int installed;
  sigset_t old_mask;
};

/* Set of everything we handle plus the tty job-control signals; blocked around fork
 * so that no child runs a parent handler before resetting its dispositions. */
static void relay_block_set(sigset_t *set) {
  sigemptyset(set);
  for (size_t i = 0; i < N_RELAY_SIGS; i++)
    sigaddset(set, k_relay_sigs[i]);
  sigaddset(set, SIGTTIN);
  sigaddset(set, SIGTTOU);
}

static int fd_above_stdio(int fd) {
  /* Keep our private fds off 0..2 so dup2() onto the std fds can never clobber them. */
  if (fd >= 0 && fd <= 2) {
    int nfd = fcntl(fd, F_DUPFD_CLOEXEC, 3);
    int e = errno;
    close(fd);
    errno = e;
    return nfd;
  }
  return fd;
}

static int make_pipe(int fds[2], int flags) {
  if (pipe2(fds, O_CLOEXEC | flags) != 0)
    return -1;
  fds[0] = fd_above_stdio(fds[0]);
  fds[1] = fd_above_stdio(fds[1]);
  if (fds[0] < 0 || fds[1] < 0) {
    if (fds[0] >= 0) close(fds[0]);
    if (fds[1] >= 0) close(fds[1]);
    return -1;
  }
  return 0;
}

/* Blocks the relay set (old mask saved), creates the self-pipe, installs handlers.
 * `pty` additionally ignores SIGTTIN/SIGTTOU: the pty parent may touch the user's
 * terminal while in the background and must get EIO instead of being stopped. */
static int sigstate_install(struct sigstate *s, int pty) {
  sigset_t block;
  relay_block_set(&block);
  if (sigprocmask(SIG_BLOCK, &block, &s->old_mask) != 0)
    return -1;
  int fds[2];
  if (make_pipe(fds, O_NONBLOCK) != 0) {
    int e = errno;
    sigprocmask(SIG_SETMASK, &s->old_mask, NULL);
    errno = e;
    return -1;
  }
  s->pipe_rd = fds[0];
  s->pipe_wr = fds[1];
  g_sigpipe_wr = s->pipe_wr;
  struct sigaction sa;
  memset(&sa, 0, sizeof sa);
  sa.sa_sigaction = relay_handler;
  sa.sa_flags = SA_SIGINFO | SA_RESTART;
  sigfillset(&sa.sa_mask);
  for (size_t i = 0; i < N_RELAY_SIGS; i++) {
    sigaction(k_relay_sigs[i], &sa, &s->old[i]);
  }
  struct sigaction ign;
  memset(&ign, 0, sizeof ign);
  ign.sa_handler = SIG_IGN;
  sigemptyset(&ign.sa_mask);
  if (pty) {
    sigaction(SIGTTIN, &ign, &s->old_ttin);
    sigaction(SIGTTOU, &ign, &s->old_ttou);
  } else {
    sigaction(SIGTTIN, NULL, &s->old_ttin);
    sigaction(SIGTTOU, NULL, &s->old_ttou);
  }
  s->installed = 1;
  return 0;
}

static void sigstate_unblock(struct sigstate *s) { sigprocmask(SIG_SETMASK, &s->old_mask, NULL); }

static void sigstate_restore(struct sigstate *s) {
  if (!s->installed)
    return;
  sigset_t block;
  relay_block_set(&block);
  sigprocmask(SIG_BLOCK, &block, NULL);
  for (size_t i = 0; i < N_RELAY_SIGS; i++)
    sigaction(k_relay_sigs[i], &s->old[i], NULL);
  sigaction(SIGTTIN, &s->old_ttin, NULL);
  sigaction(SIGTTOU, &s->old_ttou, NULL);
  g_sigpipe_wr = -1;
  close(s->pipe_rd);
  close(s->pipe_wr);
  s->installed = 0;
  sigprocmask(SIG_SETMASK, &s->old_mask, NULL);
}

/* Reads one record from the (non-blocking) self-pipe; 1 = got one, 0 = none. */
static int sigpipe_next(int fd, struct sigrec *r) {
  for (;;) {
    ssize_t n = read(fd, r, sizeof *r);
    if (n == (ssize_t)sizeof *r)
      return 1;
    if (n < 0 && errno == EINTR)
      continue;
    return 0;
  }
}

/* "Sent by a process" (kill/sigqueue/tgkill) as opposed to generated by the kernel,
 * e.g. by the terminal driver. */
static int user_sent(const struct sigrec *r) { return r->code <= 0 && r->pid > 0; }

/* Is `signo` one of the signals we relay to the command? */
static int is_forwarded(int signo) {
  switch (signo) {
  case SIGINT: case SIGQUIT: case SIGTSTP: case SIGTERM: case SIGHUP:
  case SIGALRM: case SIGUSR1: case SIGUSR2: case SIGPIPE: case SIGWINCH: case SIGCONT:
    return 1;
  default:
    return 0;
  }
}

/* Non-pty forwarding follows signal_cb_nopty: ignore user signals from the
 * command or a group led by sudo/the command; tty-generated INT/QUIT/TSTP/WINCH
 * already reach the command. SIGCONT from the invoking shell must be relayed
 * even when the command moved to a different process group.
 * Pty mode also excludes senders in the command's session.
 * `cmd_pid` is the command (non-pty) or the monitor = pty session id (pty). */
static int should_forward(const struct sigrec *r, pid_t cmd_pid, int pty) {
  if (!is_forwarded(r->signo))
    return 0;
  int from_user = user_sent(r);
  if (from_user) {
    if (r->pid == cmd_pid)
      return 0;
    if (!pty && r->pgrp != -1 &&
        (r->pgrp == cmd_pid || r->pgrp == getpid()))
      return 0;
    if (pty && r->sid != -1 && r->sid == cmd_pid)
      return 0;
  }
  if (r->signo == SIGINT || r->signo == SIGQUIT || r->signo == SIGTSTP ||
      (!pty && r->signo == SIGWINCH)) {
    if (!from_user)
      return 0;
    if (pty && r->pgrp != -1 && r->pgrp == getpgrp())
      return 0;
  }
  return 1;
}

/* ------------------------------------------------------------------------- */
/* Child side.                                                                */
/* ------------------------------------------------------------------------- */

enum stage {
  ST_SIGNALS = 1,
  ST_SETGROUPS,
  ST_SETGID,
  ST_SETUID,
  ST_VERIFY_GROUPS,
  ST_VERIFY_GID,
  ST_VERIFY_UID,
  ST_VERIFY_REGAIN_UID,
  ST_VERIFY_REGAIN_GID,
  ST_CHDIR,
  ST_EXEC,
  ST_SETSID,
  ST_CTTY,
  ST_DUP,
  ST_FORK,
  ST_APPARMOR,
  ST_CHROOT,
  ST_NOEXEC,
};

struct child_err {
  int err;
  int stage;
  long a, b; /* stage-specific details (observed ids) */
};

struct exec_req {
  const char *path;
  char **argv;   /* NULL-terminated */
  char **envp;   /* NULL-terminated */
  char **shargv; /* "sh", path, argv[1..], NULL — the ENOEXEC fallback */
  uid_t uid;
  gid_t gid;
  uid_t ruid;
  gid_t *groups;      /* as given (passed to setgroups) */
  gid_t *groups_sort; /* sorted copy for comparisons */
  size_t ngroups;
  gid_t *scratch; /* getgroups buffer, scratch_cap entries */
  int scratch_cap;
  const char *cwd; /* NULL = don't chdir */
  const char *chroot_dir; /* policy-authorized root; applied only in exec child */
  const char *noexec_file;
  mode_t umask;
  unsigned closefrom;
  int errfd; /* write end of the CLOEXEC error pipe */
  int cwd_optional;
  unsigned timeout;
  const char *apparmor;
  char *preload;
  const char *utmp_user;
  int execfd;
  int exec_background;
  struct rlimit limits[RLIM_NLIMITS];
  unsigned char limit_set[RLIM_NLIMITS];
};
static const struct { const char *name; int resource; } names[] = {
  {"rlimit_as", RLIMIT_AS}, {"rlimit_core", RLIMIT_CORE},
  {"rlimit_cpu", RLIMIT_CPU}, {"rlimit_data", RLIMIT_DATA},
  {"rlimit_fsize", RLIMIT_FSIZE}, {"rlimit_locks", RLIMIT_LOCKS},
  {"rlimit_memlock", RLIMIT_MEMLOCK}, {"rlimit_nofile", RLIMIT_NOFILE},
  {"rlimit_nproc", RLIMIT_NPROC}, {"rlimit_rss", RLIMIT_RSS},
  {"rlimit_stack", RLIMIT_STACK}
};

static void warn_limit(int resource) {
  const char *name = "unknown";
  const char *error = strerror(errno);
  for (size_t j = 0; j < sizeof names / sizeof names[0]; j++)
    if (names[j].resource == resource) name = names[j].name;
  struct iovec parts[] = {
    {(void *)"sudo: setrlimit(", sizeof("sudo: setrlimit(") - 1},
    {(void *)name, strlen(name)}, {(void *)"): ", 3},
    {(void *)error, strlen(error)}, {(void *)"\n", 1}
  };
  ssize_t ignored = writev(2, parts, 5);
  (void)ignored;
}

__attribute__((noreturn)) static void child_fail(int errfd, int stage, int err, long a, long b) {
  struct child_err ce;
  memset(&ce, 0, sizeof ce);
  ce.err = err;
  ce.stage = stage;
  ce.a = a;
  ce.b = b;
  ssize_t n = write(errfd, &ce, sizeof ce);
  (void)n;
  _exit(127);
}

/* Shell sort: async-signal-safe (no allocation), fine for group lists. */
static void sort_gids(gid_t *v, size_t n) {
  for (size_t gap = n / 2; gap > 0; gap /= 2)
    for (size_t i = gap; i < n; i++) {
      gid_t t = v[i];
      size_t j = i;
      for (; j >= gap && v[j - gap] > t; j -= gap)
        v[j] = v[j - gap];
      v[j] = t;
    }
}

/* Does the current supplementary group list equal r->groups (as a multiset)? */
static int groups_match(const struct exec_req *r) {
  int n = getgroups(r->scratch_cap, r->scratch);
  if (n < 0 || (size_t)n != r->ngroups)
    return 0;
  sort_gids(r->scratch, (size_t)n);
  for (size_t i = 0; i < r->ngroups; i++)
    if (r->scratch[i] != r->groups_sort[i])
      return 0;
  return 1;
}

static void drop_privileges(const struct exec_req *r) {
  /* setgroups needs CAP_SETGID even when nothing changes; skipping it when the list
   * already matches is safe because the result is verified below either way. */
  if (!groups_match(r) && setgroups(r->ngroups, r->groups) != 0)
    child_fail(r->errfd, ST_SETGROUPS, errno, 0, 0);
  if (setresgid(r->gid, r->gid, r->gid) != 0)
    child_fail(r->errfd, ST_SETGID, errno, 0, 0);
  struct rlimit nproc, unlimited;
  int saved_nproc = getrlimit(RLIMIT_NPROC, &nproc) == 0;
  if (saved_nproc) {
    unlimited = (struct rlimit){RLIM_INFINITY, RLIM_INFINITY};
    if (setrlimit(RLIMIT_NPROC, &unlimited) != 0) {
      unlimited.rlim_cur = unlimited.rlim_max = nproc.rlim_max;
      if (setrlimit(RLIMIT_NPROC, &unlimited) != 0) warn_limit(RLIMIT_NPROC);
    }
  }
  if (setresuid(r->ruid, r->uid, r->uid) != 0)
    child_fail(r->errfd, ST_SETUID, errno, 0, 0);
  if (saved_nproc) (void)setrlimit(RLIMIT_NPROC, &nproc);

  /* Verification: never trust the return codes alone. */
  uid_t ru, eu, su;
  gid_t rg, eg, sg;
  if (getresgid(&rg, &eg, &sg) != 0)
    child_fail(r->errfd, ST_VERIFY_GID, errno, -1, -1);
  if (rg != r->gid || eg != r->gid || sg != r->gid)
    child_fail(r->errfd, ST_VERIFY_GID, 0, (long)rg, (long)eg);
  if (getresuid(&ru, &eu, &su) != 0)
    child_fail(r->errfd, ST_VERIFY_UID, errno, -1, -1);
  if (ru != r->ruid || eu != r->uid || su != r->uid)
    child_fail(r->errfd, ST_VERIFY_UID, 0, (long)ru, (long)eu);
  if (!groups_match(r))
    child_fail(r->errfd, ST_VERIFY_GROUPS, 0, 0, 0);
  if (r->uid != 0) {
    /* With stay_setuid a real ID of zero legitimately permits restoring that
     * effective ID. Do not mutate the verified IDs by probing this case. */
    if (r->ruid != 0 && setuid(0) == 0)
      child_fail(r->errfd, ST_VERIFY_REGAIN_UID, 0, 0, 0);
    if (r->gid != 0 && setgid(0) == 0)
      child_fail(r->errfd, ST_VERIFY_REGAIN_GID, 0, 0, 0);
  }
}

/* Mark every fd >= from close-on-exec. The error pipe is already CLOEXEC, so it
 * stays usable until execve succeeds and is closed by it. */
static void cloexec_from(unsigned from) {
  if (syscall(SYS_close_range, from, ~0U, CLOSE_RANGE_CLOEXEC) == 0)
    return;
  struct rlimit rl;
  long max = 65536;
  if (getrlimit(RLIMIT_NOFILE, &rl) == 0 && rl.rlim_cur != RLIM_INFINITY && rl.rlim_cur < (rlim_t)(1L << 30))
    max = (long)rl.rlim_cur;
  for (long fd = (long)from; fd < max; fd++)
    (void)fcntl((int)fd, F_SETFD, FD_CLOEXEC);
}

/* Final part of every command child. Signals must still be blocked on entry. */
__attribute__((noreturn)) static void child_exec(const struct exec_req *r) {
  if (ls_intercept_trace_child() != 0)
    child_fail(r->errfd, ST_EXEC, errno, 0, 0);
  ls_iolog_child_close();
  if (restore_startup_signals() != 0)
    child_fail(r->errfd, ST_SIGNALS, errno, 0, 0);
  /* Like sudo, restoration is best-effort: PAM may have lowered the hard
   * limit, and Linux will not accept PR_SET_DUMPABLE=2. exec resets dumpability. */
  if (g_core_saved) (void)setrlimit(RLIMIT_CORE, &g_core_limit);
  if (g_dumpable >= 0) (void)prctl(PR_SET_DUMPABLE, g_dumpable);
  for (int i = 0; i < RLIM_NLIMITS; i++) {
    if (!r->limit_set[i]) continue;
    struct rlimit lim = r->limits[i];
    if (setrlimit(i, &lim) == 0) continue;
    /* Containers may lack CAP_SYS_RESOURCE: sudo clamps requested increases
     * to the invoking user's hard limit and then retries. */
    if (g_user_limit_saved[i]) {
      if (lim.rlim_cur > g_user_limits[i].rlim_max) lim.rlim_cur = g_user_limits[i].rlim_max;
      if (lim.rlim_max > g_user_limits[i].rlim_max) lim.rlim_max = g_user_limits[i].rlim_max;
    }
    if (setrlimit(i, &lim) != 0)
      warn_limit(i);
  }
  if (r->apparmor != NULL) {
    int current = open("/proc/self/attr/apparmor/current", O_RDONLY | O_CLOEXEC);
    if (current < 0 && errno == ENOENT)
      current = open("/proc/self/attr/current", O_RDONLY | O_CLOEXEC);
    char label;
    if (current < 0)
      child_fail(r->errfd, ST_APPARMOR, errno, 1, 0);
    ssize_t got = read(current, &label, 1);
    int readerr = errno;
    close(current);
    if (got != 1)
      child_fail(r->errfd, ST_APPARMOR, got < 0 ? readerr : EINVAL, 1, 0);
    int fd = open("/proc/self/attr/apparmor/exec", O_WRONLY | O_CLOEXEC);
    if (fd < 0 && errno == ENOENT)
      fd = open("/proc/self/attr/exec", O_WRONLY | O_CLOEXEC);
    if (fd < 0)
      child_fail(r->errfd, ST_APPARMOR, errno, 0, 0);
    size_t len = strlen(r->apparmor);
    ssize_t n = write(fd, r->apparmor, len);
    int e = errno;
    close(fd);
    if (n != (ssize_t)len)
      child_fail(r->errfd, ST_APPARMOR, n < 0 ? e : EIO, 0, 0);
  }
  /* All identity/NSS and policy work is complete before entering the root.
   * Resolve privileged fd closing outside it, as sudo's exec_setup does. */
  cloexec_from(r->closefrom);
  if (r->chroot_dir != NULL &&
      (chroot(r->chroot_dir) != 0 || chdir("/") != 0))
    child_fail(r->errfd, ST_CHROOT, errno, 0, 0);
  drop_privileges(r);
  if (r->noexec_file != NULL) {
    struct stat st;
    int fd = open(r->noexec_file, O_RDONLY | O_CLOEXEC);
    if (fd == -1)
      child_fail(r->errfd, ST_NOEXEC, errno, 0, 0);
    int rc = fstat(fd, &st);
    int saved = errno;
    close(fd);
    if (rc != 0 || !S_ISREG(st.st_mode))
      child_fail(r->errfd, ST_NOEXEC, rc != 0 ? saved : EACCES, 0, 0);
  }
  if (r->cwd != NULL && chdir(r->cwd) != 0) {
    if (!r->cwd_optional)
      child_fail(r->errfd, ST_CHDIR, errno, 0, 0);
    /* Warning only for login shells, as sudo's CD_CWD_OPTIONAL. */
    const char *es = strerror(errno);
    struct iovec parts[] = {
      {(void *)"sudo: unable to change directory to ", sizeof("sudo: unable to change directory to ") - 1},
      {(void *)r->cwd, strlen(r->cwd)}, {(void *)": ", 2},
      {(void *)es, strlen(es)}, {(void *)"\n", 1}
    };
    ssize_t ignored = writev(2, parts, 5);
    (void)ignored;
    if (r->chroot_dir != NULL) {
      ignored = write(2, "sudo: starting from /\n", sizeof("sudo: starting from /\n") - 1);
      (void)ignored;
    }
  }
  umask(r->umask);
  if (ls_intercept_dso_child() != 0)
    child_fail(r->errfd, ST_EXEC, errno, 0, 0);
  if (r->execfd >= 0) {
    /* Keep binary descriptors close-on-exec. Linux script interpreters need
     * /dev/fd/N after exec; ENOENT is the kernel's CLOEXEC-script indication. */
    if (fcntl(r->execfd, F_SETFD, FD_CLOEXEC) != 0)
      child_fail(r->errfd, ST_EXEC, errno, 0, 0);
    fexecve(r->execfd, r->argv, r->envp);
    if (errno == ENOENT) {
      if (fcntl(r->execfd, F_SETFD, 0) != 0)
        child_fail(r->errfd, ST_EXEC, errno, 0, 0);
      fexecve(r->execfd, r->argv, r->envp);
    }
  } else {
    execve(r->path, r->argv, r->envp);
  }
  if (r->execfd < 0 && errno == ENOEXEC) {
    /* Like sudo (and execvp): a file without a recognised header is a shell script. */
    execve("/bin/sh", r->shargv, r->envp);
  }
  child_fail(r->errfd, ST_EXEC, errno, 0, 0);
}

/* ------------------------------------------------------------------------- */
/* Parent helpers.                                                            */
/* ------------------------------------------------------------------------- */

static lean_obj_res io_error(const char *msg) {
  return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(msg)));
}

static lean_obj_res io_errno(const char *what, int err) {
  char buf[512];
  snprintf(buf, sizeof buf, "%s: %s", what, strerror(err));
  return io_error(buf);
}

static void describe_child_err(const struct exec_req *r, const struct child_err *ce, char *buf, size_t len) {
  const char *es = strerror(ce->err);
  switch (ce->stage) {
  case ST_SIGNALS:
    snprintf(buf, len, "unable to restore signal state: %s", es);
    break;
  case ST_SETGROUPS:
    snprintf(buf, len, "unable to set supplementary group IDs: %s", es);
    break;
  case ST_SETGID:
    snprintf(buf, len, "unable to set gid to %u: %s", (unsigned)r->gid, es);
    break;
  case ST_SETUID:
    snprintf(buf, len, "unable to set uid to %u: %s", (unsigned)r->uid, es);
    break;
  case ST_VERIFY_GROUPS:
    snprintf(buf, len, "unable to set supplementary group IDs: verification failed");
    break;
  case ST_VERIFY_GID:
    if (ce->err)
      snprintf(buf, len, "unable to change to runas gid: %s", es);
    else
      snprintf(buf, len, "unable to change to runas gid (%ld, %ld)", ce->a, ce->b);
    break;
  case ST_VERIFY_UID:
    if (ce->err)
      snprintf(buf, len, "unable to change to runas uid: %s", es);
    else
      snprintf(buf, len, "unable to change to runas uid (%ld, %ld)", ce->a, ce->b);
    break;
  case ST_VERIFY_REGAIN_UID:
    snprintf(buf, len, "unable to drop privileges: uid 0 could be regained");
    break;
  case ST_VERIFY_REGAIN_GID:
    snprintf(buf, len, "unable to drop privileges: gid 0 could be regained");
    break;
  case ST_CHROOT:
    snprintf(buf, len, "unable to change root to %s: %s", r->chroot_dir, es);
    break;
  case ST_NOEXEC:
    snprintf(buf, len, "unable to load noexec library %s: %s", r->noexec_file, es);
    break;
  case ST_CHDIR:
    snprintf(buf, len, "unable to change directory to %s: %s", r->cwd ? r->cwd : "", es);
    break;
  case ST_EXEC:
    snprintf(buf, len, "unable to execute %s: %s", r->path, es);
    break;
  case ST_SETSID:
    snprintf(buf, len, "unable to create session: %s", es);
    break;
  case ST_CTTY:
    snprintf(buf, len, "unable to set controlling tty: %s", es);
    break;
  case ST_DUP:
    snprintf(buf, len, "unable to dup2 pty: %s", es);
    break;
  case ST_FORK:
    snprintf(buf, len, "unable to fork: %s", es);
    break;
  case ST_APPARMOR:
    if (ce->a)
      snprintf(buf, len, "failed to determine AppArmor confinement: %s", es);
    else
      snprintf(buf, len, "unable to change AppArmor profile to %s: %s", r->apparmor + 5, es);
    break;
  default:
    snprintf(buf, len, "unable to execute %s: unknown error", r->path);
    break;
  }
}

/* Blocking read of the child's error report. 1 = report read, 0 = EOF (exec ok). */
static int read_child_err(int fd, struct child_err *ce) {
  size_t got = 0;
  char *p = (char *)ce;
  while (got < sizeof *ce) {
    ssize_t n = read(fd, p + got, sizeof *ce - got);
    if (n < 0) {
      if (errno == EINTR)
        continue;
      break;
    }
    if (n == 0)
      break;
    got += (size_t)n;
  }
  if (got == 0)
    return 0;
  if (got < sizeof *ce) {
    /* A partial report still means the child failed before exec: fail closed. */
    memset(ce, 0, sizeof *ce);
    ce->stage = 0;
  }
  return 1;
}

static int waitpid_retry(pid_t pid, int *status, int flags) {
  for (;;) {
    pid_t r = waitpid(pid, status, flags);
    if (r < 0 && errno == EINTR)
      continue;
    return (int)r;
  }
}

static bool last_dumped_core;

LEAN_EXPORT lean_obj_res leansudo_exec_dumped_core(lean_obj_arg world) {
  (void)world;
  return lean_io_result_mk_ok(lean_box(last_dumped_core));
}

static uint32_t encode_status(int status) {
#ifdef WCOREDUMP
  last_dumped_core = WIFSIGNALED(status) && WCOREDUMP(status);
#else
  last_dumped_core = false;
#endif
  if (WIFSIGNALED(status))
    return 0x10000u | (uint32_t)WTERMSIG(status);
  return (uint32_t)WEXITSTATUS(status);
}

/* Temporarily give `sig` its default action and deliver it to ourselves (or to our
 * whole process group, like sudo does in pty mode) so that the invoking shell sees
 * sudo stop. Returns once we have been continued. */
static void stop_self(int sig, int whole_pgrp) {
  struct sigaction dfl, old;
  memset(&dfl, 0, sizeof dfl);
  dfl.sa_handler = SIG_DFL;
  sigemptyset(&dfl.sa_mask);
  int changed = 0;
  if (sig != SIGSTOP)
    changed = sigaction(sig, &dfl, &old) == 0;
  sigset_t un;
  sigemptyset(&un);
  sigaddset(&un, sig);
  sigprocmask(SIG_UNBLOCK, &un, NULL);
  if (whole_pgrp)
    killpg(getpgrp(), sig);
  else
    /* Lean may execute us on a worker thread. A process-directed kill can
     * reach another thread after we restore the handler; raise targets this
     * thread, so the stop has happened before the disposition is restored. */
    raise(sig);
  if (changed)
    sigaction(sig, &old, NULL);
}

/* Like sudo's tcsetpgrp_nobg: do not steal the tty if sudo lost the foreground
 * between tcgetpgrp and tcsetpgrp. Catch SIGTTOU instead of blocking it. */
static volatile sig_atomic_t got_sigttou;
static void record_sigttou(int sig) {
  (void)sig;
  got_sigttou = 1;
}

static int tcsetpgrp_nobg(int fd, pid_t pgrp) {
  struct sigaction sa, old;
  memset(&sa, 0, sizeof sa);
  sa.sa_handler = record_sigttou;
  sigemptyset(&sa.sa_mask);
  got_sigttou = 0;
  if (sigaction(SIGTTOU, &sa, &old) != 0) return -1;
  int ret;
  do {
    ret = tcsetpgrp(fd, pgrp);
  } while (ret != 0 && errno == EINTR && !got_sigttou);
  int saved_errno = errno;
  sigaction(SIGTTOU, &old, NULL);
  errno = saved_errno;
  return ret;
}

/* ------------------------------------------------------------------------- */
/* Non-pty mode (cf. sudo exec_nopty.c).                                      */
/* ------------------------------------------------------------------------- */

/* sudo_suspend_parent(): a separate command pgrp stopped on terminal I/O
 * should get the foreground if sudo owns it; otherwise suspend sudo itself. */
static void nopty_child_stopped(pid_t child, int sig) {
  int ttyfd = open("/dev/tty", O_RDWR | O_NOCTTY | O_CLOEXEC);
  pid_t saved = ttyfd >= 0 ? tcgetpgrp(ttyfd) : -1;
  if (ttyfd >= 0 && saved == -1) {
    close(ttyfd);
    ttyfd = -1;
  }
  if ((sig == SIGTTIN || sig == SIGTTOU) && saved == getpgrp()) {
    pid_t command_pgrp = getpgid(child);
    if (command_pgrp > 0 && command_pgrp != getpgrp() &&
        tcsetpgrp_nobg(ttyfd, command_pgrp) == 0) {
      killpg(command_pgrp, SIGCONT);
      close(ttyfd);
      return;
    }
  }
  if (ls_iolog_suspend(sig)) {
    if (ttyfd >= 0) close(ttyfd);
    kill(child, SIGKILL);
    return;
  }
  stop_self(sig, 0);
  if (ls_iolog_suspend(SIGCONT)) kill(child, SIGKILL);
  if (ttyfd >= 0) {
    if (saved != getpgrp()) (void)tcsetpgrp_nobg(ttyfd, saved);
    close(ttyfd);
  }
}

/* Returns 1 with *status when the child terminated, 0 to keep waiting, -1 on error. */
static int nopty_reap(pid_t child, int *status) {
  for (;;) {
    int st;
    int tracing = ls_intercept_trace();
    int r = waitpid_retry(tracing ? -1 : child, &st,
        WNOHANG | WUNTRACED | WCONTINUED | (tracing ? __WALL : 0));
    if (r < 0)
      return -1;
    if (r == 0)
      return 0;
    if (tracing) {
      int consumed = ls_intercept_trace_wait((pid_t)r, st);
      if (consumed < 0) return -1;
      if (consumed || r != child) continue;
    }
    if (WIFEXITED(st) || WIFSIGNALED(st)) {
      *status = st;
      return 1;
    }
    if (WIFSTOPPED(st))
      nopty_child_stopped(child, WSTOPSIG(st));
  }
}

struct command_timer { int64_t deadline; int terminating; };

static int64_t monotonic_ms(void) {
  struct timespec ts;
  if (clock_gettime(CLOCK_MONOTONIC, &ts) != 0) return 0;
  return (int64_t)ts.tv_sec * 1000 + ts.tv_nsec / 1000000;
}

/* sudo terminates timed-out commands with HUP then TERM, followed by KILL
 * after a two-second grace period. Never signal sudo's own process group. */
static int timeout_poll(struct command_timer *t, pid_t child, int group) {
  if (!t->deadline) return -1;
  int64_t remaining = t->deadline - monotonic_ms();
  if (remaining <= 0) {
    pid_t target = group ? -child : child;
    if (!t->terminating) {
      kill(target, SIGHUP);
      kill(target, SIGTERM);
      t->terminating = 1;
      t->deadline = monotonic_ms() + 2000;
      return 2000;
    }
    kill(target, SIGKILL);
    t->deadline = 0;
    return -1;
  }
  return remaining > INT32_MAX ? INT32_MAX : (int)remaining;
}

static lean_obj_res nopty_wait(struct sigstate *ss, pid_t child, unsigned timeout) {
  int status = 0;
  struct command_timer timer = {timeout ? monotonic_ms() + (int64_t)timeout * 1000 : 0, 0};
  for (;;) {
    int r = nopty_reap(child, &status);
    if (r < 0)
      return io_errno("waitpid", errno);
    if (r == 1)
      break;
    struct pollfd pfds[6];
    pfds[0] = (struct pollfd){.fd = ss->pipe_rd, .events = POLLIN};
    io_channel_poll(pfds + 1);
    pfds[4] = (struct pollfd){.fd = ls_logsrv_queue_fd(), .events = POLLIN};
    pfds[5] = (struct pollfd){.fd = ls_logsrv_network_fd(), .events = POLLIN};
    if (poll(pfds, 6, timeout_poll(&timer, child, 0)) < 0 && errno != EINTR)
      return io_errno("poll", errno);
    if ((pfds[4].revents && ls_logsrv_dispatch()) ||
        (pfds[5].revents && ls_logsrv_poll()) || io_channel_pump(pfds + 1)) {
      int e = errno;
      kill(child, SIGKILL);
      waitpid_retry(child, &status, 0);
      return io_errno("unable to write I/O log", e);
    }
    struct sigrec rec;
    while (sigpipe_next(ss->pipe_rd, &rec)) {
      if (rec.signo == SIGCHLD)
        continue; /* reaped at the top of the loop */
      if (should_forward(&rec, child, 0))
        kill(child, rec.signo);
    }
  }
  if (ls_logsrv_dispatch()) return io_errno("unable to write remote event log", errno);
  if (io_channels_drain()) return io_errno("unable to write I/O log", errno);
  return lean_io_result_mk_ok(lean_box_uint32(encode_status(status)));
}

/* ------------------------------------------------------------------------- */
/* Pty mode (cf. sudo exec_pty.c / exec_monitor.c).                           */
/* ------------------------------------------------------------------------- */

/* Backchannel messages over a SOCK_SEQPACKET socketpair between sudo and monitor. */
enum { MSG_SIGNAL = 1, MSG_CONT_FG, MSG_CONT_BG, MSG_STOPPED, MSG_EXITED };
struct bcmsg {
  int type;
  int val;
};

struct pty_ctx {
  int ttyfd;  /* our own open of /dev/tty (the user's terminal) */
  int master; /* O_NONBLOCK */
  int slave;
  int ttymask; /* bit i set ⇔ fd i (0..2) is a tty and gets the slave */
  int fg;      /* we are in the user's terminal foreground pgrp */
  int raw;     /* user terminal is currently in raw mode (by us) */
  struct termios orig;
  int rows, cols; /* sudo_get_ttysize fallback until the first resize event */
};

static int bc_send(int sock, int type, int val) {
  struct bcmsg m = {.type = type, .val = val};
  for (;;) {
    ssize_t n = send(sock, &m, sizeof m, MSG_NOSIGNAL);
    if (n == (ssize_t)sizeof m)
      return 0;
    if (n < 0 && errno == EINTR)
      continue;
    return -1;
  }
}

/* 1 = message, 0 = EOF/error (peer gone), -1 = would block. */
static int bc_recv(int sock, struct bcmsg *m) {
  for (;;) {
    ssize_t n = recv(sock, m, sizeof *m, MSG_DONTWAIT);
    if (n == (ssize_t)sizeof *m)
      return 1;
    if (n < 0 && errno == EINTR)
      continue;
    if (n < 0 && (errno == EAGAIN || errno == EWOULDBLOCK))
      return -1;
    return 0;
  }
}

static void close_pty_ctx(struct pty_ctx *p) {
  if (p->ttyfd >= 0) close(p->ttyfd);
  if (p->master >= 0) close(p->master);
  if (p->slave >= 0) close(p->slave);
  p->ttyfd = p->master = p->slave = -1;
}

static int tty_dimension(const char *name, int fallback) {
  const unsigned char *s = (const unsigned char *)getenv(name);
  if (s == NULL) return fallback;
  while (*s == ' ' || (*s >= '\t' && *s <= '\r')) s++;
  if (*s == '+') s++;
  if (*s < '0' || *s > '9') return fallback;
  unsigned n = 0;
  while (*s >= '0' && *s <= '9') {
    unsigned digit = *s++ - '0';
    if (n > ((unsigned)INT32_MAX - digit) / 10) return fallback;
    n = n * 10 + digit;
  }
  return *s == '\0' && n != 0 ? (int)n : fallback;
}

/* Allocate the pty and mirror the user's terminal settings onto it. On failure
 * returns -1 with errno set and nothing left open. */
static int pty_setup(struct pty_ctx *p) {
  p->ttyfd = p->master = p->slave = -1;
  p->raw = 0;
  p->ttymask = 0;
  for (int fd = 0; fd <= 2; fd++)
    if (isatty(fd))
      p->ttymask |= 1 << fd;
  int e;
  p->ttyfd = open("/dev/tty", O_RDWR | O_NOCTTY | O_CLOEXEC);
  if (p->ttyfd < 0)
    return -1;
  p->ttyfd = fd_above_stdio(p->ttyfd);
  if (p->ttyfd < 0 || tcgetattr(p->ttyfd, &p->orig) != 0)
    goto fail;
  struct winsize ws;
  memset(&ws, 0, sizeof ws);
  (void)ioctl(p->ttyfd, TIOCGWINSZ, &ws);
  p->rows = ws.ws_row && ws.ws_col ? ws.ws_row : tty_dimension("LINES", 24);
  p->cols = ws.ws_row && ws.ws_col ? ws.ws_col : tty_dimension("COLUMNS", 80);
  struct termios t = p->orig;
  if (openpty(&p->master, &p->slave, NULL, &t, &ws) != 0)
    goto fail;
  if (fcntl(p->master, F_SETFD, FD_CLOEXEC) != 0 || fcntl(p->slave, F_SETFD, FD_CLOEXEC) != 0)
    goto fail;
  p->master = fd_above_stdio(p->master);
  p->slave = fd_above_stdio(p->slave);
  if (p->master < 0 || p->slave < 0)
    goto fail;
  int fl = fcntl(p->master, F_GETFL);
  if (fl < 0 || fcntl(p->master, F_SETFL, fl | O_NONBLOCK) != 0)
    goto fail;
  p->fg = tcgetpgrp(p->ttyfd) == getpgrp();
  return 0;
fail:
  e = errno;
  close_pty_ctx(p);
  errno = e;
  return -1;
}

static void tty_set_raw(struct pty_ctx *p) {
  if (p->raw || !p->fg)
    return;
  struct termios t = p->orig;
  cfmakeraw(&t);
  t.c_cc[VMIN] = 1;
  t.c_cc[VTIME] = 0;
  if (tcsetattr(p->ttyfd, TCSADRAIN, &t) == 0)
    p->raw = 1;
}

static void tty_restore(struct pty_ctx *p) {
  if (!p->raw)
    return;
  /* SIGTTOU is ignored while the pty loop runs, so this cannot stop us. */
  while (tcsetattr(p->ttyfd, TCSADRAIN, &p->orig) != 0 && errno == EINTR)
    ;
  p->raw = 0;
}

static void check_fg(struct pty_ctx *p) { p->fg = tcgetpgrp(p->ttyfd) == getpgrp(); }

static void write_all(int fd, const char *buf, size_t len) {
  while (len > 0) {
    ssize_t n = write(fd, buf, len);
    if (n < 0) {
      if (errno == EINTR)
        continue;
      if (errno == EAGAIN) {
        struct pollfd pfd = {.fd = fd, .events = POLLOUT, .revents = 0};
        (void)poll(&pfd, 1, 1000);
        continue;
      }
      return; /* terminal gone: drop output */
    }
    buf += n;
    len -= (size_t)n;
  }
}

static void utmp_text(char *dest, size_t cap, const char *src) {
  size_t n = strlen(src);
  memset(dest, 0, cap);
  memcpy(dest, src, n < cap ? n : cap);
}

static int utmp_begin(int fromfd, int tofd, const char *user, struct utmpx *entry) {
  char from[128], to[128];
  if (!user || ttyname_r(tofd, to, sizeof to) != 0) return 0;
  memset(entry, 0, sizeof *entry);
  setutxent();
  if (ttyname_r(fromfd, from, sizeof from) == 0) {
    struct utmpx key = {0};
    utmp_text(key.ut_line, sizeof key.ut_line, strncmp(from, "/dev/", 5) == 0 ? from + 5 : from);
    struct utmpx *old = getutxline(&key);
    if (old) *entry = *old;
    setutxent();
  }
  const char *line = strncmp(to, "/dev/", 5) == 0 ? to + 5 : to;
  utmp_text(entry->ut_line, sizeof entry->ut_line, line);
  size_t len = strlen(line);
  utmp_text(entry->ut_id, sizeof entry->ut_id,
      len > sizeof entry->ut_id ? line + len - sizeof entry->ut_id : line);
  utmp_text(entry->ut_user, sizeof entry->ut_user, user);
  entry->ut_type = USER_PROCESS;
  entry->ut_pid = getpid();
  entry->ut_tv.tv_sec = time(NULL);
  entry->ut_tv.tv_usec = 0;
  int ok = pututxline(entry) != NULL;
  endutxent();
  return ok;
}

static void utmp_finish(struct utmpx *entry, int status) {
  memset(entry->ut_user, 0, sizeof entry->ut_user);
  entry->ut_type = DEAD_PROCESS;
  entry->ut_exit.e_termination = WIFSIGNALED(status) ? WTERMSIG(status) : 0;
  entry->ut_exit.e_exit = WIFEXITED(status) ? WEXITSTATUS(status) : 0;
  entry->ut_tv.tv_sec = time(NULL);
  setutxent();
  (void)pututxline(entry);
  endutxent();
}

/* Monitor process: session leader of the pty. Never returns. Signals are blocked
 * on entry (inherited from sudo's fork). */
__attribute__((noreturn)) static void monitor_main(struct pty_ctx *p, int sock, int parent_sigrd, int parent_sigwr,
                                                   const struct exec_req *r) {
  /* Drop sudo's handlers; the monitor must never be stopped by job control. */
  struct sigaction sa;
  memset(&sa, 0, sizeof sa);
  sigemptyset(&sa.sa_mask);
  for (size_t i = 0; i < N_RELAY_SIGS; i++) {
    sa.sa_handler = SIG_DFL;
    sigaction(k_relay_sigs[i], &sa, NULL);
  }
  sa.sa_handler = SIG_IGN;
  sigaction(SIGTSTP, &sa, NULL);
  sigaction(SIGTTIN, &sa, NULL);
  sigaction(SIGTTOU, &sa, NULL);
  close(parent_sigrd);
  close(parent_sigwr);
  close(p->master);
  close(p->ttyfd);

  int mp[2];
  if (pipe2(mp, O_CLOEXEC | O_NONBLOCK) != 0)
    child_fail(r->errfd, ST_FORK, errno, 0, 0);
  g_sigpipe_wr = mp[1];
  memset(&sa, 0, sizeof sa);
  sa.sa_sigaction = relay_handler;
  sa.sa_flags = SA_SIGINFO | SA_RESTART;
  sigfillset(&sa.sa_mask);
  sigaction(SIGCHLD, &sa, NULL);

  if (setsid() < 0)
    child_fail(r->errfd, ST_SETSID, errno, 0, 0);
  if (ioctl(p->slave, TIOCSCTTY, 0) != 0)
    child_fail(r->errfd, ST_CTTY, errno, 0, 0);

  pid_t cmd = fork();
  if (cmd < 0)
    child_fail(r->errfd, ST_FORK, errno, 0, 0);
  if (cmd == 0) {
    /* Command: own pgrp in the pty session, foreground if sudo is. */
    close(sock);
    close(mp[0]);
    close(mp[1]);
    setpgid(0, 0);
    if (p->fg && !r->exec_background)
      (void)tcsetpgrp(p->slave, getpid()); /* SIGTTOU ignored+blocked here */
    for (int fd = 0; fd <= 2; fd++)
      if ((p->ttymask & (1 << fd)) && dup2(p->slave, fd) < 0)
        child_fail(r->errfd, ST_DUP, errno, 0, 0);
    close(p->slave);
    child_exec(r);
  }
  if (ls_intercept_trace_attach(cmd) != 0) {
    int e = errno;
    kill(cmd, SIGKILL);
    ls_intercept_trace_close();
    int status;
    (void)waitpid_retry(cmd, &status, 0);
    child_fail(r->errfd, ST_EXEC, e, 0, 0);
  }
  ls_iolog_child_close();
  for (int fd = 0; fd < 3; fd++)
    if (io_channels[fd].enabled) close(fd);
  /* Both sides call setpgid/tcsetpgrp so there is no window either way. */
  setpgid(cmd, cmd);
  if (p->fg && !r->exec_background)
    (void)tcsetpgrp(p->slave, cmd);
  close(r->errfd);

  sigset_t un;
  sigemptyset(&un);
  sigaddset(&un, SIGCHLD);
  sigprocmask(SIG_UNBLOCK, &un, NULL);

  pid_t saved_fg = -1; /* pty foreground pgrp when the command stopped */
  int sock_open = 1;
  struct command_timer timer = {r->timeout ? monotonic_ms() + (int64_t)r->timeout * 1000 : 0, 0};
  for (;;) {
    /* Reap first: SIGCHLD may predate the handler being unblocked. */
    int st;
    pid_t w;
    int tracing = ls_intercept_trace();
    while ((w = waitpid_retry(tracing ? -1 : cmd, &st,
        WNOHANG | WUNTRACED | WCONTINUED | (tracing ? __WALL : 0))) > 0) {
      if (tracing) {
        int consumed = ls_intercept_trace_wait(w, st);
        if (consumed < 0) {
          killpg(cmd, SIGKILL);
          ls_intercept_trace_close();
          _exit(1);
        }
        if (consumed || w != cmd) continue;
      }
      if (WIFSTOPPED(st)) {
        saved_fg = tcgetpgrp(p->slave);
        if (sock_open)
          bc_send(sock, MSG_STOPPED, WSTOPSIG(st));
        else
          killpg(cmd, SIGCONT); /* nobody to resume us later */
      } else if (WIFEXITED(st) || WIFSIGNALED(st)) {
        ls_intercept_trace_close();
        close(p->slave);
        if (sock_open)
          bc_send(sock, MSG_EXITED, st);
        _exit(0);
      }
    }
    if (w < 0)
      _exit(1);

    struct pollfd pfds[2] = {{.fd = mp[0], .events = POLLIN, .revents = 0},
                             {.fd = sock_open ? sock : -1, .events = POLLIN, .revents = 0}};
    if (poll(pfds, 2, timeout_poll(&timer, cmd, 1)) < 0 && errno != EINTR)
      _exit(1);
    struct sigrec rec;
    while (sigpipe_next(mp[0], &rec))
      ; /* only SIGCHLD is handled: reaped at the top of the loop */
    if (sock_open && (pfds[1].revents & (POLLIN | POLLHUP | POLLERR))) {
      struct bcmsg m;
      int got;
      while ((got = bc_recv(sock, &m)) == 1) {
        switch (m.type) {
        case MSG_SIGNAL:
          if (killpg(cmd, m.val) != 0)
            kill(cmd, m.val);
          break;
        case MSG_CONT_FG: {
          pid_t pg = (saved_fg > 0 && saved_fg != getpgrp()) ? saved_fg : cmd;
          (void)tcsetpgrp(p->slave, pg);
          if (killpg(cmd, SIGCONT) != 0)
            kill(cmd, SIGCONT);
          break;
        }
        case MSG_CONT_BG:
          /* Monitor owns the pty foreground: the command gets SIGTTIN if it reads. */
          (void)tcsetpgrp(p->slave, getpgrp());
          if (killpg(cmd, SIGCONT) != 0)
            kill(cmd, SIGCONT);
          break;
        default:
          break;
        }
      }
      if (got == 0) {
        /* sudo went away: hang up the command, keep reaping it. */
        sock_open = 0;
        close(sock);
        killpg(cmd, SIGHUP);
        killpg(cmd, SIGCONT);
      }
    }
  }
}

struct pty_loop {
  struct pty_ctx *p;
  int sock;
  pid_t monitor;
  char in[4096]; /* user tty → pty master, pending */
  size_t in_len, in_off;
  int tty_in_ok;   /* user tty still readable */
  int master_open; /* pty master still readable */
  int log_error;
};

/* The command stopped with `sig` inside the pty. */
static void pty_cmd_stopped(struct pty_loop *L, int sig) {
  struct pty_ctx *p = L->p;
  if (sig == SIGTTIN || sig == SIGTTOU) {
    /* It wanted the terminal; if we already own it, just resume in the foreground. */
    check_fg(p);
    if (p->fg) {
      tty_set_raw(p);
      bc_send(L->sock, MSG_CONT_FG, 0);
      return;
    }
  }
  tty_restore(p);
  if (ls_iolog_suspend(sig)) { L->log_error = 1; return; }
  stop_self(sig, 1);
  if (ls_iolog_suspend(SIGCONT)) { L->log_error = 1; return; }
  /* Resumed: the command follows us into the foreground or background. */
  check_fg(p);
  if (p->fg) {
    tty_set_raw(p);
    bc_send(L->sock, MSG_CONT_FG, 0);
  } else {
    bc_send(L->sock, MSG_CONT_BG, 0);
  }
}

static void pty_pump_master(struct pty_loop *L) {
  char buf[8192];
  for (;;) {
    ssize_t n = read(L->p->master, buf, sizeof buf);
    if (n > 0) {
      if (ls_iolog_write(4, buf, (size_t)n)) { L->log_error = 1; return; }
      write_all(L->p->ttyfd, buf, (size_t)n);
      continue;
    }
    if (n < 0 && errno == EINTR)
      continue;
    if (n < 0 && errno == EAGAIN)
      return;
    L->master_open = 0; /* EIO: every slave fd is closed */
    return;
  }
}

static void pty_flush_input(struct pty_loop *L) {
  while (L->in_off < L->in_len) {
    ssize_t n = write(L->p->master, L->in + L->in_off, L->in_len - L->in_off);
    if (n < 0) {
      if (errno == EINTR)
        continue;
      if (errno != EAGAIN)
        L->in_off = L->in_len; /* pty gone: drop */
      break;
    }
    L->in_off += (size_t)n;
  }
  if (L->in_off >= L->in_len)
    L->in_off = L->in_len = 0;
}

/* Main relay loop. Returns 1 with the command's wait status, 0 if the monitor died
 * without reporting one, -1 on a fatal poll error. */
static int pty_relay(struct sigstate *ss, struct pty_loop *L, int *status) {
  struct pty_ctx *p = L->p;
  int have_status = 0;
  int sock_open = 1;
  tty_set_raw(p);
  while (!have_status && sock_open) {
    struct pollfd pfds[9];
    pfds[0] = (struct pollfd){.fd = ss->pipe_rd, .events = POLLIN, .revents = 0};
    pfds[1] = (struct pollfd){.fd = L->sock, .events = POLLIN, .revents = 0};
    short mev = 0;
    if (L->master_open)
      mev |= POLLIN;
    if (L->in_len > 0)
      mev |= POLLOUT;
    pfds[2] = (struct pollfd){.fd = mev ? p->master : -1, .events = mev, .revents = 0};
    /* Read the user's terminal only while we are its foreground job. */
    int want_tty = L->tty_in_ok && p->fg && L->in_len == 0;
    pfds[3] = (struct pollfd){.fd = want_tty ? p->ttyfd : -1, .events = POLLIN, .revents = 0};
    io_channel_poll(pfds + 4);
    pfds[7] = (struct pollfd){.fd = ls_logsrv_queue_fd(), .events = POLLIN};
    pfds[8] = (struct pollfd){.fd = ls_logsrv_network_fd(), .events = POLLIN};
    if (poll(pfds, 9, -1) < 0) {
      if (errno == EINTR)
        continue;
      return -1;
    }
    if (pfds[7].revents && ls_logsrv_dispatch()) return -1;
    if (pfds[8].revents && ls_logsrv_poll()) return -1;
    if (io_channel_pump(pfds + 4)) return -1;
    if (pfds[2].revents & (POLLIN | POLLHUP | POLLERR))
      pty_pump_master(L);
    if (L->log_error) return -1;
    if (pfds[2].revents & POLLOUT)
      pty_flush_input(L);
    if (pfds[3].revents & (POLLIN | POLLHUP | POLLERR)) {
      ssize_t n = read(p->ttyfd, L->in, sizeof L->in);
      if (n > 0) {
        if (ls_iolog_write(3, L->in, (size_t)n)) return -1;
        L->in_len = (size_t)n;
        L->in_off = 0;
        pty_flush_input(L);
      } else if (n == 0 || (errno != EINTR && errno != EAGAIN)) {
        if (n < 0 && errno == EIO)
          check_fg(p); /* background read: wait for SIGCONT */
        else
          L->tty_in_ok = 0;
      }
    }
    struct sigrec rec;
    while (sigpipe_next(ss->pipe_rd, &rec)) {
      switch (rec.signo) {
      case SIGCHLD:
        break; /* the monitor reports through the backchannel */
      case SIGWINCH: {
        struct winsize ws;
        if (ioctl(p->ttyfd, TIOCGWINSZ, &ws) == 0 &&
            (ws.ws_row != p->rows || ws.ws_col != p->cols)) {
          if (ls_iolog_winsize(ws.ws_row, ws.ws_col)) return -1;
          (void)ioctl(p->master, TIOCSWINSZ, &ws);
          /* TIOCSWINSZ alone may not signal (e.g. an initially zero-sized
           * terminal). sudo explicitly signals the command pgrp as well. */
          bc_send(L->sock, MSG_SIGNAL, SIGWINCH);
          p->rows = ws.ws_row;
          p->cols = ws.ws_col;
        }
        break;
      }
      case SIGCONT: {
        /* e.g. `fg`/`bg` from the shell after we stopped, or a plain SIGCONT. */
        int was_fg = p->fg;
        check_fg(p);
        if (p->fg && !p->raw) {
          tty_set_raw(p);
          bc_send(L->sock, MSG_CONT_FG, 0);
        } else if (!p->fg && was_fg) {
          bc_send(L->sock, MSG_CONT_BG, 0);
        }
        break;
      }
      default:
        if (should_forward(&rec, L->monitor, 1))
          bc_send(L->sock, MSG_SIGNAL, rec.signo);
        break;
      }
    }
    if (pfds[1].revents & (POLLIN | POLLHUP | POLLERR)) {
      struct bcmsg m;
      int got;
      while ((got = bc_recv(L->sock, &m)) == 1) {
        if (m.type == MSG_STOPPED) {
          pty_cmd_stopped(L, m.val);
          if (L->log_error) return -1;
        } else if (m.type == MSG_EXITED) {
          *status = m.val;
          have_status = 1;
        }
      }
      if (got == 0)
        sock_open = 0;
    }
  }
  /* Drain what the command wrote before exiting. EIO arrives once all slave fds are
   * closed and the buffer is empty; the timeout covers background processes that
   * still hold the slave open. */
  while (have_status && L->master_open) {
    struct pollfd pfd = {.fd = p->master, .events = POLLIN, .revents = 0};
    int n = poll(&pfd, 1, 100);
    if (n < 0 && errno == EINTR)
      continue;
    if (n <= 0)
      break;
    pty_pump_master(L);
    if (L->log_error) return -1;
  }
  if (io_channels_drain()) return -1;
  if (ls_logsrv_dispatch()) return -1;
  tty_restore(p);
  return have_status;
}

/* ------------------------------------------------------------------------- */
/* Entry points.                                                              */
/* ------------------------------------------------------------------------- */

static void free_req(struct exec_req *r) {
  free(r->argv);
  free(r->envp);
  free(r->shargv);
  free(r->groups);
  free(r->groups_sort);
  free(r->scratch);
  free(r->preload);
  free((void *)r->apparmor);
}

static int cmp_gid(const void *a, const void *b) {
  gid_t x = *(const gid_t *)a, y = *(const gid_t *)b;
  return x < y ? -1 : x > y;
}

static char **string_array(b_lean_obj_arg arr, size_t extra_front) {
  size_t n = lean_array_size(arr);
  char **v = calloc(n + extra_front + 1, sizeof(char *));
  if (v == NULL)
    return NULL;
  for (size_t i = 0; i < n; i++)
    v[extra_front + i] = (char *)lean_string_cstr(lean_array_get_core(arr, i));
  return v;
}

static lean_obj_res run_with_req(struct exec_req *r, int use_pty, int background);

/* Parse policy limits before forking, in setrlimit's native units. */
static int limit_number(const char *s, char **end, rlim_t *value) {
  if (strncmp(s, "infinity", 8) == 0) {
    *end = (char *)s + 8; *value = RLIM_INFINITY; return 1;
  }
  if (*s < '0' || *s > '9') return 0;
  rlim_t n = 0;
  while (*s >= '0' && *s <= '9') {
    unsigned digit = (unsigned)(*s - '0');
    if (n > ((rlim_t)-1 - digit) / 10) return 0;
    n = n * 10 + digit;
    s++;
  }
  *end = (char *)s;
  *value = n;
  return 1;
}

static int prepare_options(struct exec_req *r, b_lean_obj_arg noexec,
    b_lean_obj_arg apparmor, b_lean_obj_arg limits) {
  for (size_t i = 0; i < lean_array_size(limits); i++) {
    b_lean_obj_arg pair = lean_array_get_core(limits, i);
    const char *name = lean_string_cstr(lean_ctor_get(pair, 0));
    const char *value = lean_string_cstr(lean_ctor_get(pair, 1));
    int resource = -1;
    for (size_t j = 0; j < sizeof names / sizeof names[0]; j++)
      if (strcmp(name, names[j].name) == 0) resource = names[j].resource;
    if (resource < 0) { errno = EINVAL; return 0; }
    if (strcmp(value, "default") == 0) { r->limit_set[resource] = 0; continue; }
    struct rlimit lim;
    if (strcmp(value, "user") == 0) {
      if (g_user_limit_saved[resource]) lim = g_user_limits[resource];
      else if (getrlimit(resource, &lim) != 0) return 0;
    } else {
      char *end;
      if (!limit_number(value, &end, &lim.rlim_cur)) { errno = EINVAL; return 0; }
      lim.rlim_max = lim.rlim_cur;
      if (*end == ',') {
        if (!limit_number(end + 1, &end, &lim.rlim_max)) { errno = EINVAL; return 0; }
      }
      if (*end || lim.rlim_cur > lim.rlim_max) { errno = EINVAL; return 0; }
    }
    r->limit_set[resource] = 1;
    r->limits[resource] = lim;
  }
  if (!lean_is_scalar(apparmor)) {
    /* sudo's apparmor_is_enabled deliberately checks only this module flag,
     * not securityfs (which is commonly unavailable inside containers). */
    int fd = open("/sys/module/apparmor/parameters/enabled", O_RDONLY | O_CLOEXEC);
    char enabled = 0;
    if (fd >= 0) {
      ssize_t n = read(fd, &enabled, 1);
      close(fd);
      if (n != 1) enabled = 0;
    }
    if (enabled == 'Y') {
      const char *profile = lean_string_cstr(lean_ctor_get(apparmor, 0));
      char *text;
      if (asprintf(&text, "exec %s", profile) < 0) return 0;
      r->apparmor = text;
    }
  }
  if (!lean_is_scalar(noexec)) {
    const char *file = lean_string_cstr(lean_ctor_get(noexec, 0));
    r->noexec_file = file;
    if (r->chroot_dir == NULL) {
      struct stat st;
      if (stat(file, &st) != 0) return 0;
      if (!S_ISREG(st.st_mode) || access(file, R_OK) != 0) { errno = EACCES; return 0; }
    }
    size_t n = 0, slot = 0;
    const char *old = NULL;
    for (size_t i = 0; r->envp[i]; i++) {
      if (strncmp(r->envp[i], "LD_PRELOAD=", 11) == 0) {
        if (old) continue;
        old = r->envp[i] + 11;
        slot = n;
      }
      r->envp[n++] = r->envp[i];
    }
    r->envp[n] = NULL;
    size_t filelen = strlen(file);
    if (old && strncmp(old, file, filelen) == 0 &&
        (old[filelen] == 0 || old[filelen] == ':'))
      return 1;
    /* The policy DSO must be first, ahead of any user-supplied preload. */
    if (asprintf(&r->preload, "LD_PRELOAD=%s%s%s", file,
        old && *old ? ":" : "", old ? old : "") < 0) return 0;
    if (!old) {
      char **envp = realloc(r->envp, (n + 2) * sizeof(char *));
      if (!envp) return 0;
      r->envp = envp;
      slot = n;
      r->envp[n + 1] = NULL;
    }
    r->envp[slot] = r->preload;
  }
  return 1;
}

LEAN_EXPORT lean_obj_res leansudo_exec_initialize(uint8_t disable_core, lean_obj_arg world) {
  (void)world;
  for (int fd = 0; fd < 3; fd++) {
    if (fcntl(fd, F_GETFD) >= 0 || errno != EBADF) continue;
    int nullfd = open("/dev/null", O_RDWR);
    if (nullfd < 0) return io_errno("unable to open /dev/null", errno);
    if (nullfd != fd) {
      if (dup2(nullfd, fd) < 0) {
        int e = errno; close(nullfd);
        return io_errno("unable to repair standard descriptor", e);
      }
      close(nullfd);
    }
  }
  if (lean_sudo_initialize_locale() != 0)
    return io_errno("unable to initialize locale", errno);
  if (disable_core && !g_core_saved) {
    if (getrlimit(RLIMIT_CORE, &g_core_limit) != 0)
      return io_errno("unable to read core dump limit", errno);
    struct rlimit disabled = g_core_limit;
    disabled.rlim_cur = 0;
    if (setrlimit(RLIMIT_CORE, &disabled) != 0)
      return io_errno("unable to disable core dumps", errno);
    g_core_saved = 1;
    g_dumpable = prctl(PR_GET_DUMPABLE);
    if (prctl(PR_SET_DUMPABLE, 0) != 0)
      return io_errno("unable to disable core dumps", errno);
  }
  return lean_io_result_mk_ok(lean_box(0));
}
/* runRaw : (path : @& String) → (argv env : @& Array String) → (uid gid : UInt32) →
 *   (groups : @& Array UInt32) → (cwd : @& Option String) → (umask : UInt32) →
 *   (usePty background : Bool) → (closeFrom : UInt32) → IO UInt32
 * Result: exit code, or 0x10000 | signal. Strings were checked NUL-free and ids
 * range-checked on the Lean side. */
LEAN_EXPORT lean_obj_res leansudo_exec_run(b_lean_obj_arg path, b_lean_obj_arg argv, b_lean_obj_arg env, uint32_t uid,
                                           uint32_t gid, b_lean_obj_arg groups, b_lean_obj_arg cwd, uint32_t umask_,
                                           uint8_t use_pty, uint8_t background, uint32_t closefrom,
                                           uint8_t cwd_optional, uint32_t timeout,
                                           b_lean_obj_arg noexec, b_lean_obj_arg apparmor,
                                           b_lean_obj_arg limits, b_lean_obj_arg utmp_user,
                                           uint32_t execfd, uint8_t exec_background, uint8_t stay_setuid,
                                           b_lean_obj_arg chroot_dir,
                                           lean_obj_arg world) {
  (void)world;
  last_dumped_core = false;
  struct exec_req r;
  memset(&r, 0, sizeof r);
  r.path = lean_string_cstr(path);
  r.uid = (uid_t)uid;
  /* sudo's set_user_groups does setegid(target), then setgid(invoking) as
   * root for stay_setuid. The latter sets all three GIDs to the invoking GID. */
  r.gid = stay_setuid ? g_invoking_gid : (gid_t)gid;
  r.ruid = stay_setuid ? g_invoking_uid : r.uid;
  r.umask = (mode_t)(umask_ & 0777);
  r.closefrom = closefrom < 3 ? 3 : closefrom;
  r.cwd = lean_is_scalar(cwd) ? NULL : lean_string_cstr(lean_ctor_get(cwd, 0));
  r.chroot_dir = lean_is_scalar(chroot_dir) ? NULL : lean_string_cstr(lean_ctor_get(chroot_dir, 0));
  r.errfd = -1;
  r.cwd_optional = cwd_optional;
  r.timeout = timeout;
  r.utmp_user = lean_is_scalar(utmp_user) ? NULL : lean_string_cstr(lean_ctor_get(utmp_user, 0));
  r.execfd = execfd == UINT32_MAX ? -1 : (int)execfd;
  r.exec_background = exec_background;

  size_t argc = lean_array_size(argv);
  r.ngroups = lean_array_size(groups);
  long ngmax = sysconf(_SC_NGROUPS_MAX);
  if (ngmax < 0 || ngmax > (1L << 20))
    ngmax = 65536;
  r.scratch_cap = (int)ngmax;
  r.argv = string_array(argv, 0);
  r.envp = string_array(env, 0);
  r.shargv = calloc(argc + 3, sizeof(char *));
  r.groups = malloc((r.ngroups + 1) * sizeof(gid_t));
  r.groups_sort = malloc((r.ngroups + 1) * sizeof(gid_t));
  r.scratch = malloc(((size_t)ngmax + 1) * sizeof(gid_t));
  if (!r.argv || !r.envp || !r.shargv || !r.groups || !r.groups_sort || !r.scratch) {
    free_req(&r);
    return io_error("unable to allocate memory");
  }
  r.shargv[0] = "sh";
  r.shargv[1] = (char *)r.path;
  for (size_t i = 1; i < argc; i++)
    r.shargv[i + 1] = r.argv[i];
  for (size_t i = 0; i < r.ngroups; i++) {
    r.groups[i] = (gid_t)lean_unbox_uint32(lean_array_get_core(groups, i));
    r.groups_sort[i] = r.groups[i];
  }
  qsort(r.groups_sort, r.ngroups, sizeof(gid_t), cmp_gid);
  if (!prepare_options(&r, noexec, apparmor, limits)) {
    int e = errno;
    free_req(&r);
    return io_errno("unable to configure command execution", e);
  }

  /* DSO interception modifies only the initial environment. The vector borrows
   * existing values and has its own two transport variables. */
  char **plain_env = r.envp;
  char **intercept_env = NULL;
  if (ls_intercept_active() && !ls_intercept_trace()) {
    intercept_env = ls_intercept_dso_environment(plain_env);
    if (!intercept_env) {
      int e = errno;
      free_req(&r);
      return io_errno("unable to configure command interception", e);
    }
    r.envp = intercept_env;
  }
  lean_obj_res res = run_with_req(&r, use_pty, background);
  if (intercept_env) {
    ls_intercept_dso_free_environment(intercept_env);
    r.envp = plain_env;
  }
  if (ls_iolog_close(0, 0)) {
    lean_dec(res);
    res = io_errno("unable to close I/O log", errno);
  }
  lean_obj_res remote_error = ls_logsrv_take_error();
  if (remote_error) {
    lean_dec(res);
    res = remote_error;
  }
  free_req(&r);
  return res;
}

static lean_obj_res child_error_result(const struct exec_req *r, const struct child_err *ce) {
  char buf[1024];
  describe_child_err(r, ce, buf, sizeof buf);
  return io_error(buf);
}

static lean_obj_res run_with_req(struct exec_req *r, int use_pty, int background) {
  if (background) {
    /* The original process must not unwind PAM. The forked supervisor returns
     * through Lean after waiting, and is the sole owner of session cleanup. */
    pid_t bg = fork();
    if (bg < 0)
      return io_errno("unable to fork", errno);
    if (bg > 0)
      _exit(0);
    if (setpgid(0, 0) != 0)
      return io_errno("unable to create background process group", errno);
  }
  int errp[2];
  if (make_pipe(errp, 0) != 0)
    return io_errno("unable to create pipe", errno);
  r->errfd = errp[1];

  int any_tty = isatty(0) || isatty(1) || isatty(2);
  struct pty_ctx pc;
  memset(&pc, 0, sizeof pc);
  pc.ttyfd = pc.master = pc.slave = -1;
  int sv[2] = {-1, -1};
  int pty = ((use_pty && !background) || ls_iolog_active()) && any_tty;
  if (pty) {
    int perr = 0;
    if (pty_setup(&pc) != 0) {
      perr = errno;
    } else if (socketpair(AF_UNIX, SOCK_SEQPACKET | SOCK_CLOEXEC, 0, sv) != 0) {
      perr = errno;
      close_pty_ctx(&pc);
    }
    if (perr != 0) {
      /* Fail soft, like sudo: run the command without a pty. */
      char msg[256];
      snprintf(msg, sizeof msg, "sudo: unable to allocate pty: %s\n", strerror(perr));
      write_all(2, msg, strlen(msg));
      pty = 0;
    }
  }
  if (io_channels_open(pty ? pc.ttymask : 0)) {
    int e = errno;
    close(errp[0]); close(errp[1]);
    if (pty) { close_pty_ctx(&pc); close(sv[0]); close(sv[1]); }
    return io_errno("unable to create I/O logging pipes", e);
  }

  struct sigstate ss;
  memset(&ss, 0, sizeof ss);
  if (sigstate_install(&ss, pty) != 0) {
    int e = errno;
    io_channels_close();
    close(errp[0]);
    close(errp[1]);
    if (pty) {
      close_pty_ctx(&pc);
      close(sv[0]);
      close(sv[1]);
    }
    return io_errno("unable to set up signal handlers", e);
  }
  struct utmpx utmp;
  int utmp_active = pty && utmp_begin(pc.ttyfd, pc.slave, r->utmp_user, &utmp);

  pid_t child = ls_intercept_trace_prepare() == 0 ? fork() : -1;
  if (child == 0) {
    close(errp[0]);
    for (int fd = 0; fd < 3; fd++) {
      if (io_channels[fd].child >= 0 && dup2(io_channels[fd].child, fd) < 0)
        child_fail(r->errfd, ST_DUP, errno, 0, 0);
    }
    io_channels_close();
    if (pty) {
      close(sv[0]);
      monitor_main(&pc, sv[1], ss.pipe_rd, ss.pipe_wr, r);
    }
    g_sigpipe_wr = -1;
    close(ss.pipe_rd);
    close(ss.pipe_wr);
    child_exec(r);
  }
  int fork_err = errno;
  for (int fd = 0; fd < 3; fd++) {
    if (io_channels[fd].child >= 0) close(io_channels[fd].child);
    io_channels[fd].child = -1;
  }
  close(errp[1]);
  r->errfd = -1;
  if (pty) {
    close(sv[1]);
    close(pc.slave);
    pc.slave = -1;
  }
  sigstate_unblock(&ss);

  lean_obj_res res;
  if (child < 0) {
    close(errp[0]);
    res = io_errno("unable to prepare or fork command", fork_err);
    goto out;
  }
  if (pty) {
    /* Only the monitor owns the tracees; discard our handshake descriptors. */
    ls_intercept_trace_close();
  } else if (ls_intercept_trace()) {
    if (ls_intercept_trace_attach(child) != 0) {
      int e = errno;
      kill(child, SIGKILL);
      ls_intercept_trace_close();
      int status;
      (void)waitpid_retry(child, &status, 0);
      close(errp[0]);
      res = io_errno("unable to attach command tracer", e);
      goto out;
    }
    /* The exec-error pipe cannot be read synchronously before servicing the
     * first seccomp stop. Reap/relay normally, then inspect the error report. */
    res = nopty_wait(&ss, child, r->timeout);
    ls_intercept_trace_close();
    struct child_err trace_error;
    int trace_failed = read_child_err(errp[0], &trace_error);
    close(errp[0]);
    if (trace_failed) {
      lean_dec(res);
      res = child_error_result(r, &trace_error);
    }
    goto out;
  }

  /* Phase 1: wait for execve (EOF) or a failure report. */
  struct child_err ce;
  int failed = read_child_err(errp[0], &ce);
  close(errp[0]);
  if (failed) {
    int st;
    waitpid_retry(child, &st, 0);
    res = child_error_result(r, &ce);
    goto out;
  }

  if (!pty) {
    res = nopty_wait(&ss, child, r->timeout);
    goto out;
  }

  {
    struct pty_loop L;
    memset(&L, 0, sizeof L);
    L.p = &pc;
    L.sock = sv[0];
    L.monitor = child;
    L.tty_in_ok = 1;
    L.master_open = 1;
    int status = 0;
    int got = pty_relay(&ss, &L, &status);
    int relay_errno = errno;
    if (got < 0) bc_send(sv[0], MSG_SIGNAL, SIGKILL);
    int mst;
    waitpid_retry(child, &mst, 0);
    if (got == 1)
      res = lean_io_result_mk_ok(lean_box_uint32(encode_status(status)));
    else if (got == 0)
      res = io_error("command monitor exited unexpectedly");
    else
      res = io_errno("I/O relay", relay_errno);
  }

out:
  ls_intercept_trace_close();
  if (utmp_active) {
    uint32_t code = lean_io_result_is_ok(res) ? lean_unbox_uint32(lean_io_result_get_value(res)) : 1;
    int status = code >= 0x10000 ? (int)(code - 0x10000) : (int)(code << 8);
    utmp_finish(&utmp, status);
  }
  io_channels_close();
  if (pty) {
    tty_restore(&pc);
    close_pty_ctx(&pc);
    close(sv[0]);
  }
  sigstate_restore(&ss);
  return res;
}

/* exitRaw : (signal : Bool) → (n : UInt32) → IO Unit — never returns. */
LEAN_EXPORT lean_obj_res leansudo_exec_exit(uint8_t is_signal, uint32_t n, lean_obj_arg world) {
  (void)world;
  if (is_signal && n >= 1 && n < (uint32_t)NSIG && n != SIGSTOP && n != SIGTSTP && n != SIGTTIN && n != SIGTTOU) {
    int sig = (int)n;
    /* Re-raise like sudo: default action, unblocked, without dumping our core. */
    struct rlimit rl = {0, 0};
    setrlimit(RLIMIT_CORE, &rl);
    struct sigaction sa;
    memset(&sa, 0, sizeof sa);
    sa.sa_handler = SIG_DFL;
    sigemptyset(&sa.sa_mask);
    sigaction(sig, &sa, NULL);
    sigset_t set;
    sigemptyset(&set);
    sigaddset(&set, sig);
    sigprocmask(SIG_UNBLOCK, &set, NULL);
    kill(getpid(), sig);
  }
  if (is_signal)
    exit(n > 127 ? 255 : (int)(n + 128));
  exit(n > 255 ? 255 : (int)n);
}
