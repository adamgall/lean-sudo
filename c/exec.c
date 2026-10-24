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
 *     verify (getres[ug]id, getgroups, setuid(0) must fail) → chdir → umask →
 *     mark fds >= closefrom close-on-exec → execve.
 *   - Any failure in the child is reported through a CLOEXEC pipe as (errno, stage);
 *     EOF on that pipe means execve succeeded.
 *   - The parent's signal handlers only write a record to a non-blocking self-pipe;
 *     all decisions are taken in the main loop.
 *   - In pty mode the user's terminal is always restored before sudo stops itself and
 *     before runCommand returns.
 */
#include <lean/lean.h>

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
#include <sys/syscall.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <termios.h>
#include <unistd.h>

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

__attribute__((constructor)) static void leansudo_exec_save_signals(void) {
  struct sigaction sa;
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
    /* In non-pty mode the command shares our terminal, so SIGWINCH reaches it
     * directly; we only need it to resize the pty. */
    if (!pty && k_relay_sigs[i] == SIGWINCH) {
      sigaction(SIGWINCH, NULL, &s->old[i]);
      continue;
    }
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
  case SIGALRM: case SIGUSR1: case SIGUSR2: case SIGPIPE:
    return 1;
  default:
    return 0;
  }
}

/* Forwarding policy shared by both modes.
 *  - SIGINT/SIGQUIT/SIGTSTP: only when sent by a process, and not by one in our own
 *    process group (a terminal- or pgrp-wide signal already reached the command).
 *  - never forward a signal sent by the command itself (or, in pty mode, by anything
 *    in the command's session) — that would bounce it straight back.
 * `cmd_pid` is the command (non-pty) or the monitor = pty session id (pty). */
static int should_forward(const struct sigrec *r, pid_t cmd_pid, int pty) {
  if (!is_forwarded(r->signo))
    return 0;
  int from_user = user_sent(r);
  if (from_user) {
    if (r->pid == cmd_pid)
      return 0;
    if (pty && r->sid != -1 && r->sid == cmd_pid)
      return 0;
  }
  if (r->signo == SIGINT || r->signo == SIGQUIT || r->signo == SIGTSTP) {
    if (!from_user)
      return 0;
    if (r->pgrp != -1 && r->pgrp == getpgrp())
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
  gid_t *groups;      /* as given (passed to setgroups) */
  gid_t *groups_sort; /* sorted copy for comparisons */
  size_t ngroups;
  gid_t *scratch; /* getgroups buffer, scratch_cap entries */
  int scratch_cap;
  const char *cwd; /* NULL = don't chdir */
  mode_t umask;
  unsigned closefrom;
  int errfd; /* write end of the CLOEXEC error pipe */
};

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
  if (setresuid(r->uid, r->uid, r->uid) != 0)
    child_fail(r->errfd, ST_SETUID, errno, 0, 0);

  /* Verification: never trust the return codes alone. */
  uid_t ru, eu, su;
  gid_t rg, eg, sg;
  if (getresgid(&rg, &eg, &sg) != 0)
    child_fail(r->errfd, ST_VERIFY_GID, errno, -1, -1);
  if (rg != r->gid || eg != r->gid || sg != r->gid)
    child_fail(r->errfd, ST_VERIFY_GID, 0, (long)rg, (long)eg);
  if (getresuid(&ru, &eu, &su) != 0)
    child_fail(r->errfd, ST_VERIFY_UID, errno, -1, -1);
  if (ru != r->uid || eu != r->uid || su != r->uid)
    child_fail(r->errfd, ST_VERIFY_UID, 0, (long)ru, (long)eu);
  if (!groups_match(r))
    child_fail(r->errfd, ST_VERIFY_GROUPS, 0, 0, 0);
  if (r->uid != 0) {
    /* With a non-root uid, regaining root must be impossible. */
    if (setuid(0) == 0)
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
  if (restore_startup_signals() != 0)
    child_fail(r->errfd, ST_SIGNALS, errno, 0, 0);
  drop_privileges(r);
  if (r->cwd != NULL && chdir(r->cwd) != 0)
    child_fail(r->errfd, ST_CHDIR, errno, 0, 0);
  umask(r->umask);
  cloexec_from(r->closefrom);
  execve(r->path, r->argv, r->envp);
  if (errno == ENOEXEC) {
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

static uint32_t encode_status(int status) {
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
    kill(getpid(), sig);
  if (changed)
    sigaction(sig, &old, NULL);
}

/* tcsetpgrp from a possibly-background process without being stopped by SIGTTOU. */
static void tcsetpgrp_nostop(int fd, pid_t pgrp) {
  sigset_t set, old;
  sigemptyset(&set);
  sigaddset(&set, SIGTTOU);
  sigprocmask(SIG_BLOCK, &set, &old);
  (void)tcsetpgrp(fd, pgrp);
  sigprocmask(SIG_SETMASK, &old, NULL);
}

/* ------------------------------------------------------------------------- */
/* Non-pty mode (cf. sudo exec_nopty.c).                                      */
/* ------------------------------------------------------------------------- */

/* Child stopped (e.g. ^Z reached its and our pgrp, or it got SIGSTOP/SIGTTIN):
 * stop ourselves with the same signal, then resume the command. */
static void nopty_child_stopped(pid_t child, int sig) {
  /* If the command put itself into the terminal's foreground (a job-control shell),
   * remember that so it can be restored on resume; most shells reset it themselves. */
  int ttyfd = open("/dev/tty", O_RDWR | O_NOCTTY | O_CLOEXEC);
  pid_t saved = -1;
  if (ttyfd >= 0) {
    saved = tcgetpgrp(ttyfd);
    if (saved == getpgrp())
      saved = -1;
  }
  stop_self(sig, 0);
  if (ttyfd >= 0) {
    if (saved != -1)
      tcsetpgrp_nostop(ttyfd, saved);
    close(ttyfd);
  }
  kill(child, SIGCONT);
}

/* Returns 1 with *status when the child terminated, 0 to keep waiting, -1 on error. */
static int nopty_reap(pid_t child, int *status) {
  for (;;) {
    int st;
    int r = waitpid_retry(child, &st, WNOHANG | WUNTRACED | WCONTINUED);
    if (r < 0)
      return -1;
    if (r == 0)
      return 0;
    if (WIFEXITED(st) || WIFSIGNALED(st)) {
      *status = st;
      return 1;
    }
    if (WIFSTOPPED(st))
      nopty_child_stopped(child, WSTOPSIG(st));
  }
}

static lean_obj_res nopty_wait(struct sigstate *ss, pid_t child) {
  int status = 0;
  for (;;) {
    int r = nopty_reap(child, &status);
    if (r < 0)
      return io_errno("waitpid", errno);
    if (r == 1)
      break;
    struct pollfd pfd = {.fd = ss->pipe_rd, .events = POLLIN, .revents = 0};
    if (poll(&pfd, 1, -1) < 0 && errno != EINTR)
      return io_errno("poll", errno);
    struct sigrec rec;
    while (sigpipe_next(ss->pipe_rd, &rec)) {
      if (rec.signo == SIGCHLD || rec.signo == SIGCONT)
        continue; /* reaped at the top of the loop */
      if (should_forward(&rec, child, 0))
        kill(child, rec.signo);
    }
  }
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
    if (p->fg)
      (void)tcsetpgrp(p->slave, getpid()); /* SIGTTOU ignored+blocked here */
    for (int fd = 0; fd <= 2; fd++)
      if ((p->ttymask & (1 << fd)) && dup2(p->slave, fd) < 0)
        child_fail(r->errfd, ST_DUP, errno, 0, 0);
    close(p->slave);
    child_exec(r);
  }
  /* Both sides call setpgid/tcsetpgrp so there is no window either way. */
  setpgid(cmd, cmd);
  if (p->fg)
    (void)tcsetpgrp(p->slave, cmd);
  close(r->errfd);

  sigset_t un;
  sigemptyset(&un);
  sigaddset(&un, SIGCHLD);
  sigprocmask(SIG_UNBLOCK, &un, NULL);

  pid_t saved_fg = -1; /* pty foreground pgrp when the command stopped */
  int sock_open = 1;
  for (;;) {
    /* Reap first: SIGCHLD may predate the handler being unblocked. */
    int st;
    pid_t w;
    while ((w = waitpid_retry(cmd, &st, WNOHANG | WUNTRACED | WCONTINUED)) > 0) {
      if (WIFSTOPPED(st)) {
        saved_fg = tcgetpgrp(p->slave);
        if (sock_open)
          bc_send(sock, MSG_STOPPED, WSTOPSIG(st));
        else
          killpg(cmd, SIGCONT); /* nobody to resume us later */
      } else if (WIFEXITED(st) || WIFSIGNALED(st)) {
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
    if (poll(pfds, 2, -1) < 0 && errno != EINTR)
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
  stop_self(sig, 1);
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
    struct pollfd pfds[4];
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
    if (poll(pfds, 4, -1) < 0) {
      if (errno == EINTR)
        continue;
      return -1;
    }
    if (pfds[2].revents & (POLLIN | POLLHUP | POLLERR))
      pty_pump_master(L);
    if (pfds[2].revents & POLLOUT)
      pty_flush_input(L);
    if (pfds[3].revents & (POLLIN | POLLHUP | POLLERR)) {
      ssize_t n = read(p->ttyfd, L->in, sizeof L->in);
      if (n > 0) {
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
        if (ioctl(p->ttyfd, TIOCGWINSZ, &ws) == 0)
          (void)ioctl(p->master, TIOCSWINSZ, &ws);
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
  }
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

/* runRaw : (path : @& String) → (argv env : @& Array String) → (uid gid : UInt32) →
 *   (groups : @& Array UInt32) → (cwd : @& Option String) → (umask : UInt32) →
 *   (usePty background : Bool) → (closeFrom : UInt32) → IO UInt32
 * Result: exit code, or 0x10000 | signal. Strings were checked NUL-free and ids
 * range-checked on the Lean side. */
LEAN_EXPORT lean_obj_res leansudo_exec_run(b_lean_obj_arg path, b_lean_obj_arg argv, b_lean_obj_arg env, uint32_t uid,
                                           uint32_t gid, b_lean_obj_arg groups, b_lean_obj_arg cwd, uint32_t umask_,
                                           uint8_t use_pty, uint8_t background, uint32_t closefrom,
                                           lean_obj_arg world) {
  (void)world;
  struct exec_req r;
  memset(&r, 0, sizeof r);
  r.path = lean_string_cstr(path);
  r.uid = (uid_t)uid;
  r.gid = (gid_t)gid;
  r.umask = (mode_t)(umask_ & 0777);
  r.closefrom = closefrom < 3 ? 3 : closefrom;
  r.cwd = lean_is_scalar(cwd) ? NULL : lean_string_cstr(lean_ctor_get(cwd, 0));
  r.errfd = -1;

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

  lean_obj_res res = run_with_req(&r, use_pty, background);
  free_req(&r);
  return res;
}

static lean_obj_res child_error_result(const struct exec_req *r, const struct child_err *ce) {
  char buf[1024];
  describe_child_err(r, ce, buf, sizeof buf);
  return io_error(buf);
}

static lean_obj_res run_with_req(struct exec_req *r, int use_pty, int background) {
  int errp[2];
  if (make_pipe(errp, 0) != 0)
    return io_errno("unable to create pipe", errno);
  r->errfd = errp[1];

  int any_tty = isatty(0) || isatty(1) || isatty(2);
  struct pty_ctx pc;
  memset(&pc, 0, sizeof pc);
  pc.ttyfd = pc.master = pc.slave = -1;
  int sv[2] = {-1, -1};
  int pty = use_pty && any_tty && !background;
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

  struct sigstate ss;
  memset(&ss, 0, sizeof ss);
  if (!background) {
    if (sigstate_install(&ss, pty) != 0) {
      int e = errno;
      close(errp[0]);
      close(errp[1]);
      if (pty) {
        close_pty_ctx(&pc);
        close(sv[0]);
        close(sv[1]);
      }
      return io_errno("unable to set up signal handlers", e);
    }
  } else {
    /* No handlers, but block anyway so the child starts with a known mask state. */
    sigset_t block;
    relay_block_set(&block);
    sigprocmask(SIG_BLOCK, &block, &ss.old_mask);
  }

  pid_t child = fork();
  if (child == 0) {
    close(errp[0]);
    if (pty) {
      close(sv[0]);
      monitor_main(&pc, sv[1], ss.pipe_rd, ss.pipe_wr, r);
    }
    if (!background) {
      g_sigpipe_wr = -1;
      close(ss.pipe_rd);
      close(ss.pipe_wr);
    }
    child_exec(r);
  }
  int fork_err = errno;
  close(errp[1]);
  r->errfd = -1;
  if (pty) {
    close(sv[1]);
    close(pc.slave);
    pc.slave = -1;
  }
  if (background)
    sigprocmask(SIG_SETMASK, &ss.old_mask, NULL);
  else
    sigstate_unblock(&ss);

  lean_obj_res res;
  if (child < 0) {
    close(errp[0]);
    res = io_errno("unable to fork", fork_err);
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

  if (background) {
    /* `-b`: don't wait; the child is reaped by init once we exit. */
    res = lean_io_result_mk_ok(lean_box_uint32(0));
    goto out;
  }

  if (!pty) {
    res = nopty_wait(&ss, child);
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
    int mst;
    waitpid_retry(child, &mst, 0);
    if (got == 1)
      res = lean_io_result_mk_ok(lean_box_uint32(encode_status(status)));
    else if (got == 0)
      res = io_error("command monitor exited unexpectedly");
    else
      res = io_errno("poll", errno);
  }

out:
  if (pty) {
    tty_restore(&pc);
    close_pty_ctx(&pc);
    close(sv[0]);
  }
  if (!background)
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
