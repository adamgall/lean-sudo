/-!
# Command execution (`c/exec.c`)

`runCommand` forks, drops privileges in the child in the order
setgroups → setresgid → setresuid, verifies the drop (`getres[ug]id`, `getgroups`,
and — for a non-root target — that `setuid(0)` fails), then `chdir`, `umask`, marks
fds ≥ `closeFrom` close-on-exec and `execve`s. Any failure before a successful
`execve` is reported through a close-on-exec pipe and raised here as an
`IO.userError` (sudo-style text, e.g. `unable to execute /x: No such file or directory`);
the child never runs the command in that case.

The parent relays signals and job-control stops to the command (see `c/exec.c`),
optionally through a pty (`usePty`, only when one of fds 0–2 is a terminal), and
returns the command's status.

Before anything reaches C, this module checks the arguments and fails closed:
ids must fit in `uid_t`/`gid_t` and must not be `(uid_t)-1` (which `setresuid`
treats as "unchanged"), strings must not contain NUL (C would truncate them),
`path` must be absolute, `argv` non-empty, `umask ≤ 0o777`, `closeFrom ≥ 3`.
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
  unless cSafe s.path && s.argv.all cSafe && s.env.all cSafe && (s.cwd.map cSafe).getD true do
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
  pure { uid, gid, groups, umask := s.umask.toUInt32, closeFrom := s.closeFrom.toUInt32 }

@[extern "leansudo_exec_run"]
opaque runRaw (path : @& String) (argv : @& Array String) (env : @& Array String)
    (uid gid : UInt32) (groups : @& Array UInt32) (cwd : @& Option String) (umask : UInt32)
    (usePty background : Bool) (closeFrom : UInt32) : IO UInt32

@[extern "leansudo_exec_exit"]
opaque exitRaw (isSignal : Bool) (n : UInt32) : IO Unit

/-- Flush Lean's buffered stdout/stderr; errors (e.g. a closed pipe) are ignored. -/
def flushStd : IO Unit := do
  try (← IO.getStdout).flush catch _ => pure ()
  try (← IO.getStderr).flush catch _ => pure ()

end Exec

/-- fork, drop privileges in the child in the order setgroups → setresgid → setresuid,
verify the drop with getres[ug]id (abort if it did not take), chdir, umask, close fds,
execve. The parent relays signals, waits, and returns the child's status. A failed
execve is reported back through a CLOEXEC pipe as an `IO.userError`.
With `background` the command is not waited for and `.exited 0` is returned once it
has been exec'd. -/
def runCommand (s : ExecSpec) : IO ExitStatus := do
  let c ← match Exec.check s with
    | .ok c => pure c
    | .error e => throw (IO.userError e)
  Exec.flushStd
  let r ← Exec.runRaw s.path s.argv s.env c.uid c.gid c.groups s.cwd c.umask
    s.usePty s.background c.closeFrom
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
