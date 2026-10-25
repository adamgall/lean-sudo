/-!
# Command execution (`c/exec.c`)

`runCommand` forks, marks fds ≥ `closeFrom` close-on-exec, optionally changes
the child's root, then drops privileges in the order
setgroups → setresgid → setresuid. It verifies the drop (`getres[ug]id`, `getgroups`,
and — unless the target or retained real UID is root — that `setuid(0)` fails),
then applies `chdir`, `umask`, and `execve`. Any failure before a successful
`execve` is reported through a close-on-exec pipe and raised here as an
`IO.userError` (sudo-style text, e.g. `unable to execute /x: No such file or directory`);
the child never runs the command in that case.

The parent relays signals and job-control stops to the command (see `c/exec.c`),
optionally through a pty (`usePty`, only when one of fds 0–2 is a terminal), and
returns the command's status.
Non-pty job control hands the foreground terminal to a separately grouped command
stopped by SIGTTIN/SIGTTOU, or suspends sudo until the invoking shell resumes it.
Foreground restoration refuses to steal a terminal from another job.
The invoking shell's SIGCONT is relayed to the command even in a separate process
group; command-originated signals are filtered rather than bounced back.
User-generated SIGWINCH is relayed without a pty; with a pty, size changes update
the terminal and explicitly signal the command's process group, as sudo does.

Before anything reaches C, this module checks the arguments and fails closed:
ids must fit in `uid_t`/`gid_t` and must not be `(uid_t)-1` (which `setresuid`
treats as "unchanged"), strings must not contain NUL (C would truncate them),
`path` must be absolute, `argv` non-empty, `umask ≤ 0o777`, `closeFrom ≥ 3`.

The shell calls `initializeProcess` before privileged file access. Child execution
restores the saved dump settings and applies policy resource limits (core defaults
to 0,0); login cwd failures warn, while required cwd failures abort. NOEXEC loads
the configured sudo noexec DSO and refuses an absent or unreadable library,
including a library absent from the selected chroot. AppArmor profiles
are ignored when the kernel module is disabled; enabled transitions fail closed.
Both execution modes enforce command deadlines with
HUP/TERM followed by KILL after two seconds. Backgrounding forks the supervisor,
not just the command, so PAM cleanup occurs only after completion.
`staySetuid` retains the invoking real UID captured at process startup; effective
and saved UIDs and supplementary groups remain the policy target. All three GIDs
use the invoking real GID, matching sudo's setegid(target) → setgid(invoking) order.
All six real/effective/saved IDs are checked after the transition. PAM and the
command environment still describe the target; shells may voluntarily drop the
effective IDs when they differ from the real IDs, just as with sudo.

CHROOT is applied only in the final command child, after policy/PAM and all NSS
lookups, before dropping UIDs. Pre-policy command facts use root-prefixed paths,
matching sudo 1.9.17p2 rather than changing the privileged policy process's root
(CVE-2025-32463). The child starts at `/` and then applies any requested cwd.
Root-prefixed canonical command and parent paths must remain inside the selected
root; an escaping absolute symlink is refused before the command is authorized.
The shell expands tilde roots using host passwd facts and retains each deciding
root's command identity, descriptor, digest, arguments, and set-id mode separately.
An unoverridden `CHROOT=*` is the host namespace for every lookup fact, including
canonical parents and digests; a caller-created directory named `*` is irrelevant.
-/

namespace LeanSudo.Sys

structure ExecSpec where
  /-- absolute path passed to execve -/
  path : String
  /-- including argv[0] -/
  argv : Array String
  /-- "KEY=VALUE" -/
  env : Array String
  uid : Nat
  gid : Nat
  /-- supplementary groups (setgroups) -/
  groups : Array Nat
  /-- chdir after dropping privileges -/
  cwd : Option String
  umask : Nat
  /-- only honoured when a std fd is a tty -/
  usePty : Bool
  /-- `-b` -/
  background : Bool
  closeFrom : Nat := 3
  cwdOptional : Bool := false
  timeout : Nat := 0
  noexecFile : Option String := none
  apparmorProfile : Option String := none
  rlimits : Array (String × String) := #[("rlimit_core", "0,0")]
  utmpUser : Option String := none
  execFd : Option Nat := none
  execBackground : Bool := false
  /-- Retain invoking real UID and all GIDs; effective/saved UID still use uid. -/
  staySetuid : Bool := false
  /-- Authorized chroot directory, entered only in the final command child. -/
  chroot : Option String := none
  deriving Repr, Inhabited

inductive ExitStatus where
  | exited (code : Nat)
  | signaled (sig : Nat)
  deriving Repr, BEq, DecidableEq, Inhabited

namespace Exec

/-- Largest id we accept: `(uid_t)-1 = 0xFFFFFFFF` means "no change" to `setresuid`/
`setresgid`, so it must never be passed through. -/
def maxId : Nat := 0xFFFFFFFE

/-- Range-checked conversion of a user/group id to the C type. -/
def toId? (n : Nat) : Option UInt32 :=
  if n ≤ maxId then some n.toUInt32 else none

theorem toUInt32_toNat_of_lt {n : Nat} (h : n < 4294967296) : n.toUInt32.toNat = n := by
  rw [Nat.toUInt32, UInt32.toNat_ofNat']
  omega

theorem toId?_some {n : Nat} {v : UInt32} (h : toId? n = some v) :
    v.toNat = n ∧ n ≤ maxId := by
  unfold toId? at h
  split at h
  · rename_i hle
    cases h
    unfold maxId at hle
    exact ⟨toUInt32_toNat_of_lt (by omega), hle⟩
  · cases h

/-- `toId?` never yields the "unchanged" sentinel `(uid_t)-1`. -/
theorem toId?_ne_sentinel {n : Nat} {v : UInt32} (h : toId? n = some v) :
    v ≠ 0xFFFFFFFF := by
  have ⟨hv, hle⟩ := toId?_some h
  intro heq
  subst heq
  unfold maxId at hle
  simp at hv
  omega

/-- Decoding of the C result: exit code, or `0x10000 ||| signal`. -/
def decodeStatus (r : UInt32) : ExitStatus :=
  if r.toNat ≥ 0x10000 then .signaled (r.toNat - 0x10000) else .exited r.toNat

theorem decodeStatus_exited (c : Nat) (h : c < 0x10000) :
    decodeStatus c.toUInt32 = .exited c := by
  have hc := toUInt32_toNat_of_lt (n := c) (by omega)
  unfold decodeStatus
  rw [hc]
  split
  · omega
  · rfl

theorem decodeStatus_signaled (s : Nat) (h : s < 0x10000) :
    decodeStatus (0x10000 + s).toUInt32 = .signaled s := by
  have hc := toUInt32_toNat_of_lt (n := 0x10000 + s) (by omega)
  unfold decodeStatus
  rw [hc, Nat.add_sub_cancel_left]
  split
  · rfl
  · omega

/-- Strings handed to C must not contain NUL. -/
def cSafe (s : String) : Bool := !s.contains '\x00'

/-- Only private descriptors represent pinned executables; never permit a
standard descriptor or the sentinel used to select pathname execution. -/
def validExecFd : Option Nat → Bool
  | none => true
  | some fd => decide (3 ≤ fd ∧ fd ≤ 0x7FFFFFFF)

theorem validExecFd_some {fd : Nat} (h : validExecFd (some fd) = true) :
    3 ≤ fd ∧ fd ≤ 0x7FFFFFFF := by
  simpa [validExecFd] using h

theorem validExecFd_exact {fd : Nat} (h : validExecFd (some fd) = true) :
    fd.toUInt32.toNat = fd ∧ fd.toUInt32 ≠ 0xFFFFFFFF := by
  have hb := validExecFd_some h
  have he := toUInt32_toNat_of_lt (n := fd) (by omega)
  refine ⟨he, ?_⟩
  intro hs
  rw [hs] at he
  simp at he
  omega

/-- Validated, C-ready form of an `ExecSpec`. -/
structure Checked where
  uid : UInt32
  gid : UInt32
  groups : Array UInt32
  umask : UInt32
  closeFrom : UInt32

/-- All argument checks; `.error msg` means nothing is executed. -/
def check (s : ExecSpec) : Except String Checked := do
  unless s.path.startsWith "/" do
    throw s!"unable to execute {s.path}: path is not absolute"
  unless cSafe s.path && s.argv.all cSafe && s.env.all cSafe &&
      (s.cwd.map cSafe).getD true && (s.chroot.map cSafe).getD true &&
      (s.noexecFile.map cSafe).getD true &&
      (s.apparmorProfile.map cSafe).getD true && (s.utmpUser.map cSafe).getD true &&
      s.rlimits.all (fun (k, v) => cSafe k && cSafe v) do
    throw s!"unable to execute {s.path}: argument contains a NUL byte"
  if s.argv.isEmpty then
    throw s!"unable to execute {s.path}: empty argument vector"
  let some uid := toId? s.uid | throw s!"invalid uid {s.uid}"
  let some gid := toId? s.gid | throw s!"invalid gid {s.gid}"
  let groups ← s.groups.mapM fun g =>
    match toId? g with
    | some v => pure v
    | none => throw s!"invalid gid {g}"
  unless s.umask ≤ 0o777 do
    throw s!"invalid umask {s.umask}"
  unless 3 ≤ s.closeFrom ∧ s.closeFrom ≤ 0x7FFFFFFF do
    throw s!"invalid closefrom value {s.closeFrom}"
  unless s.timeout ≤ 0x7FFFFFFF do
    throw "invalid command timeout"
  unless validExecFd s.execFd do
    throw "invalid executable descriptor"
  pure { uid, gid, groups, umask := s.umask.toUInt32, closeFrom := s.closeFrom.toUInt32 }

/-- Retaining invoking real IDs cannot bypass any checked target-ID or argument
constraint; the same validation applies in both credential modes. -/
theorem check_staySetuid (s : ExecSpec) (stay : Bool) :
    check { s with staySetuid := stay } = check s := by
  rfl

@[extern "leansudo_exec_run"]
opaque runRaw (path : @& String) (argv : @& Array String) (env : @& Array String)
    (uid gid : UInt32) (groups : @& Array UInt32) (cwd : @& Option String) (umask : UInt32)
    (usePty background : Bool) (closeFrom : UInt32) (cwdOptional : Bool) (timeout : UInt32)
    (noexecFile apparmorProfile : @& Option String) (rlimits : @& Array (String × String))
    (utmpUser : @& Option String) (execFd : UInt32) (execBackground staySetuid : Bool)
    (chroot : @& Option String) : IO UInt32

@[extern "leansudo_exec_exit"]
opaque exitRaw (isSignal : Bool) (n : UInt32) : IO Unit

/-- Flush Lean's buffered stdout/stderr; errors (e.g. a closed pipe) are ignored. -/
def flushStd : IO Unit := do
  try (← IO.getStdout).flush catch _ => pure ()
  try (← IO.getStderr).flush catch _ => pure ()

end Exec

/-- Repair standard descriptors before opening privileged files, and optionally
disable core dumps for the privileged process (restored only in the exec child). -/
@[extern "leansudo_exec_initialize"]
opaque initializeProcess (disableCoredump : Bool := true) : IO Unit

/-- Core-dump bit from the command's most recent wait status (not its monitor). -/
@[extern "leansudo_exec_dumped_core"] opaque lastDumpedCore : IO Bool

/-- fork, drop privileges in the child in the order setgroups → setresgid → setresuid,
verify the drop with getres[ug]id (abort if it did not take), chdir, umask, close fds,
execve. The parent relays signals, waits, and returns the child's status. A failed
execve is reported back through a CLOEXEC pipe as an `IO.userError`.
With `background`, the original process exits immediately; a background supervisor
waits and returns here, keeping the caller's PAM session alive until completion. -/
def runCommand (s : ExecSpec) : IO ExitStatus := do
  let c ← match Exec.check s with
    | .ok c => pure c
    | .error e => throw (IO.userError e)
  Exec.flushStd
  let r ← Exec.runRaw s.path s.argv s.env c.uid c.gid c.groups s.cwd c.umask
    s.usePty s.background c.closeFrom s.cwdOptional s.timeout.toUInt32
    s.noexecFile s.apparmorProfile s.rlimits s.utmpUser
    (s.execFd.map Nat.toUInt32 |>.getD 0xFFFFFFFF) s.execBackground s.staySetuid s.chroot
  pure (Exec.decodeStatus r)

/-- exit(code) or re-raise the signal on ourselves with default disposition
(falling back to exit(128+sig)). Lean's stdout/stderr are flushed first.
Exit codes above 255 are clamped to 255 so a failure can never wrap to 0. -/
def exitWith (s : ExitStatus) : IO α := do
  Exec.flushStd
  match s with
  | .exited c => Exec.exitRaw false (min c 255).toUInt32
  | .signaled n => Exec.exitRaw true (min n 0xFFFF).toUInt32
  throw (IO.userError "exit failed")

end LeanSudo.Sys
