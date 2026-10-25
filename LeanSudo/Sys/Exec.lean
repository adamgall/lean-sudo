namespace LeanSudo.Sys

structure ExecSpec where
  path : String
  argv : Array String
  env : Array String
  uid : Nat
  gid : Nat
  groups : Array Nat
  cwd : Option String
  umask : Nat
  usePty : Bool
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
  staySetuid : Bool := false
  chroot : Option String := none
  deriving Repr, Inhabited

inductive ExitStatus where
  | exited (code : Nat)
  | signaled (sig : Nat)
  deriving Repr, BEq, DecidableEq, Inhabited

namespace Exec

def maxId : Nat := 0xFFFFFFFE

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

theorem toId?_ne_sentinel {n : Nat} {v : UInt32} (h : toId? n = some v) :
    v ≠ 0xFFFFFFFF := by
  have ⟨hv, hle⟩ := toId?_some h
  intro heq
  subst heq
  unfold maxId at hle
  simp at hv
  omega

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

def cSafe (s : String) : Bool := !s.contains '\x00'

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

structure Checked where
  uid : UInt32
  gid : UInt32
  groups : Array UInt32
  umask : UInt32
  closeFrom : UInt32

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

def flushStd : IO Unit := do
  try (← IO.getStdout).flush catch _ => pure ()
  try (← IO.getStderr).flush catch _ => pure ()

end Exec

@[extern "leansudo_exec_initialize"]
opaque initializeProcess (disableCoredump : Bool := true) : IO Unit

@[extern "leansudo_exec_restore_core_limit"]
opaque restoreCoreLimit : IO Unit

@[extern "leansudo_exec_dumped_core"] opaque lastDumpedCore : IO Bool

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

def exitWith (s : ExitStatus) : IO α := do
  Exec.flushStd
  match s with
  | .exited c => Exec.exitRaw false (min c 255).toUInt32
  | .signaled n => Exec.exitRaw true (min n 0xFFFF).toUInt32
  throw (IO.userError "exit failed")

end LeanSudo.Sys
