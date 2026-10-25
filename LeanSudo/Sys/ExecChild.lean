import LeanSudo.Helper
import LeanSudo.Sys.ExecPlan
import LeanSudo.Sys.Prim.CoreFacts

namespace LeanSudo.Sys.Exec

open Lean
open Prim
open Prim.Exec

structure ChildPlan where
  spec : ExecSpec
  ruid : Nat
  gid : Nat
  errorFd : Nat
  redirects : Array (Nat × Nat) := #[]
  closeFds : Array Nat := #[]
  keepFds : Array Nat := #[]
  limits : Array (Nat × Nat × Nat × Nat) := #[]
  coreLimit : Option (Nat × Nat) := none
  dumpable : Int := -1
  ignored : Array Nat := #[]
  seccompFilter : Array Nat := #[]
  gate : Option Nat := none
  session : Bool := false
  slave : Option Nat := none
  foreground : Bool := false
  commandGroup : Bool := false
  deriving ToJson, FromJson

structure ChildError where
  message : String
  error : Nat := 0
  deriving ToJson, FromJson

def specOfPlan (plan : Core.ExecPlan) (env : Array String) : ExecSpec := {
  plan.toRunPlan.toSpec plan.path plan.argv.toArray env plan.uid plan.gid plan.groups with
  background := plan.background, execFd := plan.execFd, staySetuid := plan.staySetuid }

theorem specOfPlan_ids (plan : Core.ExecPlan) (env : Array String) :
    (specOfPlan plan env).uid = plan.uid ∧ (specOfPlan plan env).gid = plan.gid ∧
    (specOfPlan plan env).groups = plan.groups.toArray := by
  exact ⟨rfl, rfl, rfl⟩

theorem childPlan_ids (plan : Core.ExecPlan) (env : Array String) (child : ChildPlan)
    (h : child.spec = specOfPlan plan env) :
    child.spec.uid = plan.uid ∧ child.spec.gid = plan.gid ∧
      child.spec.groups = plan.groups.toArray := by
  rw [h]
  exact specOfPlan_ids plan env

def commandAuthorized (plan : Helper.Credentials) (actual : Helper.Verification) : Bool :=
  (Helper.authorize plan actual).isSome

theorem commandAuthorized_requires_verification (plan : Helper.Credentials)
    (actual : Helper.Verification) (h : commandAuthorized plan actual = true) :
    Helper.verified plan actual = true := by
  simp [commandAuthorized, Helper.authorize] at h
  exact h

def errnoFailure (message : String) (error : UInt32) : IO α := do
  throw (IO.userError s!"{message}: {← Prim.Exec.strerror error}")

def checkErr (message : String) (error : UInt32) : IO Unit := do
  if error != 0 then errnoFailure message error

def checkResult (message : String) (result : Int64) : IO UInt32 := do
  if result < 0 then errnoFailure message (-result).toInt.toNat.toUInt32
  return result.toInt.toNat.toUInt32

def closeQuiet (fd : UInt32) : IO Unit := do
  try Prim.Exec.close fd catch _ => pure ()

def stderr (message : String) : IO Unit := Prim.Exec.writeAll 2 message.toUTF8

def cloexecFrom (first : UInt32) : IO Unit := do
  if (← Prim.Exec.closeRange first 0xFFFFFFFF (K.CLOSE_RANGE_CLOEXEC ())) == 0 then return
  let maximum ← try
      let (limit, _) ← Prim.Exec.getrlimit (K.RLIMIT_NOFILE ())
      pure (if limit.toNat < 1073741824 then limit.toNat else 65536)
    catch _ => pure 65536
  for fd in [first.toNat:maximum] do
    discard <| Prim.Exec.fcntl fd.toUInt32 (K.F_SETFD ()) (K.FD_CLOEXEC ())

def limitNames : Array (String × UInt32) := #[
  ("rlimit_as", (K.RLIMIT_AS ())),
  ("rlimit_core", (K.RLIMIT_CORE ())),
  ("rlimit_cpu", (K.RLIMIT_CPU ())),
  ("rlimit_data", (K.RLIMIT_DATA ())),
  ("rlimit_fsize", (K.RLIMIT_FSIZE ())),
  ("rlimit_locks", (K.RLIMIT_LOCKS ())),
  ("rlimit_memlock", (K.RLIMIT_MEMLOCK ())),
  ("rlimit_nofile", (K.RLIMIT_NOFILE ())),
  ("rlimit_nproc", (K.RLIMIT_NPROC ())),
  ("rlimit_rss", (K.RLIMIT_RSS ())),
  ("rlimit_stack", (K.RLIMIT_STACK ()))]

def limitNumber (text : String) : Option Nat :=
  if text == "infinity" then some (K.RLIM_INFINITY ()).toNat
  else do
    let n ← text.toNat?
    if n ≤ (K.RLIM_INFINITY ()).toNat then some n else none

def parseLimit (text : String) : Option (Nat × Nat) := do
  match text.splitOn "," with
  | [one] => let n ← limitNumber one; pure (n, n)
  | [low, high] =>
    let a ← limitNumber low
    let b ← limitNumber high
    if a ≤ b then some (a, b) else none
  | _ => none

def mergePreload (env : Array String) (file : String) : Array String := Id.run do
  let mut out := #[]
  let mut slot : Option Nat := none
  let mut previous := ""
  for entry in env do
    if entry.startsWith "LD_PRELOAD=" then
      if slot.isSome then continue
      slot := some out.size
      previous := String.ofList (entry.toList.drop 11)
    out := out.push entry
  if previous == file || previous.startsWith (file ++ ":") then return out
  let entry := "LD_PRELOAD=" ++ file ++ (if previous.isEmpty then "" else ":" ++ previous)
  match slot with
  | some index => return out.set! index entry
  | none => return out.push entry

def warnLimit (resource : UInt32) (error : UInt32) : IO Unit := do
  let name := ((limitNames.find? (·.2 == resource)).map (·.1)).getD "unknown"
  stderr s!"sudo: setrlimit({name}): {← Prim.Exec.strerror error}\n"

def readFirst (path : String) : IO (Option UInt8) := do
  let fd ← Prim.Exec.openFile path (K.O_CLOEXEC ()) 0
  if fd < 0 then return none
  try
    let (error, bytes) ← Prim.Exec.read fd.toInt.toNat.toUInt32 1
    return if error == 0 then bytes[0]? else none
  finally closeQuiet fd.toInt.toNat.toUInt32

private def apparmor (profile : String) : IO Unit := do
  let mut current ← Prim.Exec.openFile "/proc/self/attr/apparmor/current" (K.O_CLOEXEC ()) 0
  if current == -(Int64.ofInt (K.ENOENT ()).toNat) then
    current ← Prim.Exec.openFile "/proc/self/attr/current" (K.O_CLOEXEC ()) 0
  let fd ← checkResult "failed to determine AppArmor confinement" current
  let (error, label) ← try Prim.Exec.read fd 1 finally closeQuiet fd
  if error != 0 || label.size != 1 then
    errnoFailure "failed to determine AppArmor confinement"
      (if error != 0 then error else (K.EINVAL ()))
  let mut target ← Prim.Exec.openFile "/proc/self/attr/apparmor/exec"
    ((K.O_CLOEXEC ()) ||| (K.O_WRONLY ())) 0
  if target == -(Int64.ofInt (K.ENOENT ()).toNat) then
    target ← Prim.Exec.openFile "/proc/self/attr/exec"
      ((K.O_CLOEXEC ()) ||| (K.O_WRONLY ())) 0
  let message := s!"unable to change AppArmor profile to {profile}"
  let fd ← checkResult message target
  let bytes := ("exec " ++ profile).toUTF8
  let (error, count) ← try Prim.Exec.write fd bytes 0 bytes.size.toUInt32 finally closeQuiet fd
  if error != 0 || count.toNat != bytes.size then
    errnoFailure message (if error != 0 then error else (K.EIO ()))

private def noexec (file : String) : IO Unit := do
  let message := s!"unable to load noexec library {file}"
  let fd ← checkResult message (← Prim.Exec.openFile file (K.O_CLOEXEC ()) 0)
  try
    let facts ← Prim.Exec.fstat fd
    if facts[2]! &&& (K.S_IFMT ()) != (K.S_IFREG ()) then errnoFailure message (K.EACCES ())
  finally closeQuiet fd

private def execute (plan : ChildPlan) : IO UInt32 := do
  let checked ← match check plan.spec with
    | .ok value => pure value
    | .error error => throw (IO.userError error)
  if plan.ruid > maxId || plan.gid > maxId then throw (IO.userError "invalid helper identity")
  if plan.session then discard <| checkResult "unable to create session" (← Prim.Exec.setsid)
  if plan.commandGroup then checkErr "unable to create process group" (← Prim.Exec.setpgid 0 0)
  if let some slave := plan.slave then
    if plan.session then
      checkErr "unable to set controlling tty" (← Prim.Exec.ctty slave.toUInt32)
    if plan.foreground then
      discard <| Prim.Exec.tcsetpgrp slave.toUInt32 (← Prim.Exec.getpid)
  for (source, target) in plan.redirects do
    try Prim.Exec.dup2 source.toUInt32 target.toUInt32 catch error =>
      throw (IO.userError s!"unable to dup2 pty: {error}")
  for fd in plan.closeFds do closeQuiet fd.toUInt32
  if let some gate := plan.gate then
    let (error, byte) ← Prim.Exec.read gate.toUInt32 1
    closeQuiet gate.toUInt32
    if error != 0 || byte.size != 1 then errnoFailure "unable to prepare command tracer" (K.EIO ())
  if !plan.seccompFilter.isEmpty then
    let bytes := ByteArray.mk (plan.seccompFilter.map Nat.toUInt8)
    unless bytes.size % (K.filterSize ()) == 0 && bytes.size / (K.filterSize ()) ≤ 4096 do
      throw (IO.userError "invalid seccomp program")
    checkErr s!"unable to execute {plan.spec.path}" (← Prim.Exec.seccomp bytes)
  if let some (low, high) := plan.coreLimit then
    let error ← Prim.Exec.setrlimit (K.RLIMIT_CORE ()) low.toUInt64 high.toUInt64
    if error != 0 then warnLimit (K.RLIMIT_CORE ()) error
  if plan.dumpable >= 0 then
    discard <| Prim.Exec.prctl (K.PR_SET_DUMPABLE ()) plan.dumpable.toNat.toUInt64
  for (resource, low, high, userMax) in plan.limits do
    let error ← Prim.Exec.setrlimit resource.toUInt32 low.toUInt64 high.toUInt64
    if error != 0 then
      let error ← Prim.Exec.setrlimit resource.toUInt32 (min low userMax).toUInt64
        (min high userMax).toUInt64
      if error != 0 then warnLimit resource.toUInt32 error
  if let some profile := plan.spec.apparmorProfile then apparmor profile
  cloexecFrom checked.closeFrom
  for fd in plan.keepFds do discard <| Prim.Exec.fcntl fd.toUInt32 (K.F_SETFD ()) 0
  if let some root := plan.spec.chroot then
    checkErr s!"unable to change root to {root}" (← Prim.Exec.chroot root)
    checkErr s!"unable to change root to {root}" (← Prim.Exec.chdir "/")
  let savedNproc ← try pure (some
    (← Prim.Exec.getrlimit (K.RLIMIT_NPROC ()))) catch _ => pure none
  if let some (_, maximum) := savedNproc then
    let error ← Prim.Exec.setrlimit (K.RLIMIT_NPROC ()) (K.RLIM_INFINITY ()) (K.RLIM_INFINITY ())
    if error != 0 then
      let error ← Prim.Exec.setrlimit (K.RLIMIT_NPROC ()) maximum maximum
      if error != 0 then warnLimit (K.RLIMIT_NPROC ()) error
  Helper.dropCredentials checked.uid plan.gid.toUInt32 checked.groups
    (some plan.ruid.toUInt32) true (threadOnly := true)
  if let some (low, high) := savedNproc then
    discard <| Prim.Exec.setrlimit (K.RLIMIT_NPROC ()) low high
  if let some file := plan.spec.noexecFile then noexec file
  if let some cwd := plan.spec.cwd then
    let error ← Prim.Exec.chdir cwd
    if error != 0 then
      if !plan.spec.cwdOptional then errnoFailure s!"unable to change directory to {cwd}" error
      stderr s!"sudo: unable to change directory to {cwd}: {← Prim.Exec.strerror error}\n"
      if plan.spec.chroot.isSome then stderr "sudo: starting from /\n"
  discard <| Prim.Exec.umask checked.umask
  let credentials : Helper.Credentials := {
    uid := checked.uid, gid := plan.gid.toUInt32, groups := checked.groups,
    ruid := plan.ruid.toUInt32 }
  let actual : Helper.Verification := {
    uids := (← Prim.Exec.getresuid), gids := (← Prim.Exec.getresgid)
    fsuid := (← Prim.Exec.fsuid), fsgid := (← Prim.Exec.fsgid)
    groups := (← Prim.Exec.getgroups), regainedUid := false, regainedGid := false }
  unless commandAuthorized credentials actual do
    throw (IO.userError "unable to drop privileges: verification failed")
  discard <| checkResult "command error pipe"
    (← Prim.Exec.fcntl plan.errorFd.toUInt32 (K.F_SETFD ()) (K.FD_CLOEXEC ()))
  for signal in [1:(K.NSIG ())] do
    if Prim.Exec.supportedSignal signal &&
        signal != (K.SIGKILL ()).toNat && signal != (K.SIGSTOP ()).toNat then
      discard <| Prim.Exec.signalAction signal.toUInt32
        (if plan.ignored.contains signal then Prim.Exec.ignoreHandler ()
          else Prim.Exec.defaultHandler ())
  Prim.Exec.signalMask (← Helper.inheritedMask)
  let mut error ← if let some fd := plan.spec.execFd then
      discard <| checkResult s!"unable to execute {plan.spec.path}"
        (← Prim.Exec.fcntl fd.toUInt32 (K.F_SETFD ()) (K.FD_CLOEXEC ()))
      let error ← Prim.Exec.fexecve fd.toUInt32 plan.spec.argv plan.spec.env
      if error == (K.ENOENT ()) then
        discard <| checkResult s!"unable to execute {plan.spec.path}"
          (← Prim.Exec.fcntl fd.toUInt32 (K.F_SETFD ()) 0)
        Prim.Exec.fexecve fd.toUInt32 plan.spec.argv plan.spec.env
      else pure error
    else Prim.Exec.execve plan.spec.path plan.spec.argv plan.spec.env
  if plan.spec.execFd.isNone && error == (K.ENOEXEC ()) then
    error ← Prim.Exec.execve "/bin/sh" (#["sh", plan.spec.path] ++ plan.spec.argv.extract 1
      plan.spec.argv.size) plan.spec.env
  let failure : ChildError := {
    message := s!"unable to execute {plan.spec.path}: {← Prim.Exec.strerror error}"
    error := error.toNat }
  Prim.Exec.writeAll plan.errorFd.toUInt32 (toJson failure).compress.toUTF8
  return 127

def childHelper (json : Json) : IO UInt32 := do
  let .ok plan := (fromJson? json : Except String ChildPlan) | return 127
  Prim.CoreFacts.setlocale
  try execute plan catch error =>
    let failure : ChildError := { message := error.toString }
    try Prim.Exec.writeAll plan.errorFd.toUInt32 (toJson failure).compress.toUTF8
    catch _ => pure ()
    return 127

end LeanSudo.Sys.Exec
