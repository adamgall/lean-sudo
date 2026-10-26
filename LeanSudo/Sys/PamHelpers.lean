import LeanSudo.Helper
import LeanSudo.Sys.ExecChild
import LeanSudo.Sys.Limits
import LeanSudo.Sys.Prim.Pam

namespace LeanSudo.Sys.PamHelpers

open Lean Prim.Posix
open Prim.Pam (errorCode invalidFd)
namespace E
export Prim.Exec (pipe close dup2 openFile restoreSignalMask waitpid kill getuid getgid
  getgroups writeAll readSignal signalFd)
end E

@[extern "lean_pam_chdir"] private opaque chdir (path : @& String) : IO Int
@[extern "lean_pam_exec_inherited"] private opaque execInherited
    (path : @& String) (args : USize) : IO Int

private def withArgv (args : Array ByteArray) (action : USize → IO α) : IO α := do
  let pointerSize := Prim.Plugins.pointerSize ()
  let argv ← Prim.Plugins.alloc ((args.size + 1).toUSize * pointerSize)
  if argv == 0 then throw (IO.userError "unable to allocate memory")
  let allocated ← IO.mkRef (#[] : Array USize)
  try
    for i in [:args.size] do
      let value ← Prim.Plugins.dupBytes args[i]!
      if value == 0 then throw (IO.userError "unable to allocate memory")
      allocated.modify (·.push value)
      Prim.Plugins.writePtr argv (i.toUSize * pointerSize) value
    action argv
  finally
    for value in ← allocated.get do Prim.Plugins.free value
    Prim.Plugins.free argv

private structure Plan where
  uid : Nat
  gid : Nat
  groups : Array Nat
  path : String
  args : Array String := #[]
  prompt : Array Nat := #[]
  descriptor : Nat := 0
  failure : String := ""
  limits : Array Limits.Restoration := #[]
  deriving ToJson, FromJson

private def validPlan (descriptorMax : Nat) (plan : Plan) : Bool :=
  plan.uid < UInt32.size - 1 && plan.gid < UInt32.size - 1 &&
    plan.groups.all (· < UInt32.size - 1) && plan.descriptor ≤ descriptorMax &&
    !plan.path.contains '\x00' && plan.args.all (fun value => !value.contains '\x00') &&
    plan.prompt.all (fun byte => byte > 0 && byte < 256)

theorem validPlan_iff (descriptorMax : Nat) (plan : Plan) :
    validPlan descriptorMax plan = true ↔
      plan.uid < UInt32.size - 1 ∧ plan.gid < UInt32.size - 1 ∧
      (∀ group ∈ plan.groups, group < UInt32.size - 1) ∧
      plan.descriptor ≤ descriptorMax ∧ plan.path.contains '\x00' = false ∧
      (∀ arg ∈ plan.args, arg.contains '\x00' = false) ∧
      (∀ byte ∈ plan.prompt, 0 < byte ∧ byte < 256) := by
  simp [validPlan, Array.all_eq_true, Array.forall_mem_iff_forall_getElem, and_assoc]

theorem validPlan_rejects_uid (descriptorMax : Nat) (plan : Plan)
    (h : UInt32.size - 1 ≤ plan.uid) : validPlan descriptorMax plan = false := by
  apply Bool.eq_false_iff.mpr
  intro accepted
  have safe := (validPlan_iff descriptorMax plan).mp accepted
  omega

theorem validPlan_rejects_gid (descriptorMax : Nat) (plan : Plan)
    (h : UInt32.size - 1 ≤ plan.gid) : validPlan descriptorMax plan = false := by
  apply Bool.eq_false_iff.mpr
  intro accepted
  have safe := (validPlan_iff descriptorMax plan).mp accepted
  omega

theorem validPlan_rejects_group (descriptorMax : Nat) (plan : Plan) (group : Nat)
    (member : group ∈ plan.groups) (h : UInt32.size - 1 ≤ group) :
    validPlan descriptorMax plan = false := by
  apply Bool.eq_false_iff.mpr
  intro accepted
  have safe := ((validPlan_iff descriptorMax plan).mp accepted).2.2.1 group member
  omega

theorem validPlan_rejects_descriptor (descriptorMax : Nat) (plan : Plan)
    (h : descriptorMax < plan.descriptor) : validPlan descriptorMax plan = false := by
  apply Bool.eq_false_iff.mpr
  intro accepted
  have safe := (validPlan_iff descriptorMax plan).mp accepted
  omega

theorem validPlan_rejects_path_nul (descriptorMax : Nat) (plan : Plan)
    (h : plan.path.contains '\x00' = true) : validPlan descriptorMax plan = false := by
  simp [validPlan, h]

theorem validPlan_rejects_arg_nul (descriptorMax : Nat) (plan : Plan) (arg : String)
    (member : arg ∈ plan.args) (h : arg.contains '\x00' = true) :
    validPlan descriptorMax plan = false := by
  apply Bool.eq_false_iff.mpr
  intro accepted
  have safe := ((validPlan_iff descriptorMax plan).mp accepted).2.2.2.2.2.1 arg member
  simp [h] at safe

theorem validPlan_rejects_prompt_byte (descriptorMax : Nat) (plan : Plan) (byte : Nat)
    (member : byte ∈ plan.prompt) (h : byte = 0 ∨ 256 ≤ byte) :
    validPlan descriptorMax plan = false := by
  apply Bool.eq_false_iff.mpr
  intro accepted
  have safe := ((validPlan_iff descriptorMax plan).mp accepted).2.2.2.2.2.2 byte member
  omega

private def decode (json : Json) : IO Plan := do
  let plan ← IO.ofExcept (fromJson? json)
  unless validPlan (INT_MAX ()).toNat plan do throw (IO.userError "invalid helper plan")
  return plan

private def drop (plan : Plan) : IO Unit :=
  Helper.dropCredentials plan.uid.toUInt32 plan.gid.toUInt32 (plan.groups.map Nat.toUInt32)

private def openNull (flags : UInt32) : IO UInt32 := do
  let fd ← E.openFile "/dev/null" flags 0
  if fd < 0 then throw (IO.userError "unable to open /dev/null")
  return fd.toInt.toNat.toUInt32

private def execPlan (plan : Plan) : IO UInt32 := do
  Exec.cloexecFrom (STDERR_FILENO () + 1)
  E.restoreSignalMask (← Helper.inheritedMask)
  let _ ← withArgv (plan.args.map String.toUTF8) (execInherited plan.path)
  return 127

private def askpassChild (json : Json) : IO UInt32 := do
  let plan ← decode json
  try
    E.dup2 plan.descriptor.toUInt32 (STDOUT_FILENO ())
    E.dup2 (← openNull (O_RDONLY ())) (STDIN_FILENO ())
    Exec.cloexecFrom (STDERR_FILENO () + 1)
    Limits.restoreFrom "sudo" plan.limits
    Limits.unlimitNproc "sudo"
    drop plan
    Limits.restoreNproc none
    E.restoreSignalMask (← Helper.inheritedMask)
    let args := #[plan.path.toUTF8, ByteArray.mk (plan.prompt.map Nat.toUInt8)]
    let rc ← withArgv args (execInherited plan.path)
    let reason ← Prim.Exec.strerror rc.natAbs.toUInt32
    try E.writeAll (STDERR_FILENO ()) (plan.failure ++ ": " ++ reason ++ "\n").toUTF8
    catch _ => pure ()
    return 127
  catch _ => return 126

private def mailChild (json : Json) : IO UInt32 := do
  let plan ← decode json
  try
    E.dup2 plan.descriptor.toUInt32 (STDIN_FILENO ())
    let null ← openNull (O_RDWR ())
    E.dup2 null (STDOUT_FILENO ())
    E.dup2 null (STDERR_FILENO ())
    drop plan
    if (← chdir "/") != 0 then return 126
    execPlan plan
  catch _ => return 126

private def adminChild (json : Json) : IO UInt32 := do
  let plan ← decode json
  try
    drop plan
    let flags := O_WRONLY () ||| O_CREAT () ||| O_EXCL () ||| O_NOFOLLOW () ||| O_CLOEXEC ()
    let mode := S_IRUSR () ||| S_IWUSR () ||| S_IRGRP () ||| S_IROTH ()
    let fd ← E.openFile plan.path flags mode
    if fd.toInt == errorCode (EEXIST ()) then return 0
    if fd < 0 then return 1
    E.close fd.toInt.toNat.toUInt32
    return 0
  catch _ => return 1

def register : IO Unit := do
  Helper.register "pam-askpass" askpassChild
  Helper.register "pam-mail" mailChild
  Helper.register "pam-admin" adminChild

private partial def wait (pid : UInt32) : IO UInt32 := do
  let (result, status) ← E.waitpid pid 0
  if result.toInt == errorCode (EINTR ()) then return ← wait pid
  if result < 0 then throw (IO.userError (← Prim.Exec.strerror (-result).toInt.toNat.toUInt32))
  return status

private def quietClose (fd : UInt32) : IO Unit := do
  try E.close fd catch _ => pure ()

private partial def askpassLoop (fd : UInt32) (deadline : Nat)
    (bytes : ByteArray := ByteArray.empty) : IO (Int × ByteArray) := do
  let now ← IO.monoMsNow
  if deadline != 0 && now >= deadline then return (3, ByteArray.empty)
  let timeout := if deadline == 0 then invalidFd ()
    else (min (deadline - now) (INT_MAX ()).toNat).toUInt32
  let ready ← Prim.Pam.poll fd timeout (← Prim.Pam.sigemptyset)
  if ready == errorCode (EINTR ()) then return ← askpassLoop fd deadline bytes
  if ready == 0 then return (3, ByteArray.empty)
  if ready < 0 then return (5, ByteArray.empty)
  let (count, input) ← Prim.Pam.read fd 1
  if count == errorCode (EINTR ()) then return ← askpassLoop fd deadline bytes
  if count < 0 then return (5, ByteArray.empty)
  if count == 0 then return (if bytes.isEmpty || bytes[0]! == 0 then 4 else 0, bytes)
  if input[0]! == 10 || input[0]! == 13 then return (0, bytes)
  let bytes := bytes.push input[0]!
  if bytes.size >= 1023 then return (0, bytes)
  askpassLoop fd deadline bytes

def readAskpass (path : String) (prompt : ByteArray) (uid gid : UInt32)
    (groups : Array UInt32) (timeout : UInt32) (failure : String) : IO (Int × ByteArray) := do
  let descriptors ← try pure (some (← E.pipe (O_CLOEXEC ()))) catch _ => pure none
  let some (reader, writer) := descriptors | return (5, ByteArray.empty)
  let plan : Plan := {
    uid := uid.toNat
    gid := gid.toNat
    groups := groups.map UInt32.toNat
    path := path
    prompt := prompt.data.map UInt8.toNat
    descriptor := writer.toNat
    failure
    limits := ← Limits.pending }
  let spawned ← try pure (some (← Helper.spawn "pam-askpass" (toJson plan) #[writer]))
    catch _ => pure none
    finally quietClose writer
  let some child := spawned | quietClose reader; return (5, ByteArray.empty)
  let result ← try
      let deadline ← if timeout == 0 then pure 0
        else pure ((← IO.monoMsNow) + timeout.toNat * 1000)
      askpassLoop reader deadline
    catch _ => pure (5, ByteArray.empty)
    finally quietClose reader
  if result.1 != 0 && result.1 != 4 then let _ ← E.kill child (SIGKILL ()); pure ()
  try
    let _ ← wait child
    return result
  catch _ => return (5, ByteArray.empty)

def createAdminFlag (path : String) (uid gid : UInt32) (groups : Array UInt32) : IO Unit := do
  let plan : Plan := {
    uid := uid.toNat
    gid := gid.toNat
    groups := groups.map UInt32.toNat
    path := path }
  unless validPlan (INT_MAX ()).toNat plan do
    throw (IO.userError "invalid admin flag arguments")
  let child ← Helper.spawn "pam-admin" (toJson plan)
  if (← wait child) != 0 then throw (IO.userError "unable to create admin flag")

def validMailInput (path : String) (args : Array String) (body : String) : Bool :=
  !(path.contains '\x00' || body.contains '\x00' || args.any (·.contains '\x00'))

theorem validMailInput_iff (path : String) (args : Array String) (body : String) :
    validMailInput path args body = true ↔
      path.contains '\x00' = false ∧ body.contains '\x00' = false ∧
      ∀ arg ∈ args, arg.contains '\x00' = false := by
  simp [validMailInput, Array.forall_mem_iff_forall_getElem, and_assoc]

theorem validMailInput_rejects_nul (path : String) (args : Array String) (body : String)
    (h : path.contains '\x00' = true ∨ body.contains '\x00' = true ∨
      ∃ arg ∈ args, arg.contains '\x00' = true) : validMailInput path args body = false := by
  apply Bool.eq_false_iff.mpr
  intro accepted
  have safe := (validMailInput_iff path args body).mp accepted
  rcases h with h | h | ⟨arg, member, h⟩
  · simp [h] at safe
  · simp [h] at safe
  · have clean := safe.2.2 arg member
    simp [h] at clean

def sendMail (path : String) (args : Array String) (body : String) : IO Unit := do
  unless validMailInput path args body do
    throw (IO.userError "argument contains a NUL byte")
  if args.size > 63 then throw (IO.userError "too many mailer flags")
  let uid ← E.getuid
  let gid ← E.getgid
  let groups ← try E.getgroups catch _ => throw (IO.userError "unable to get mailer groups")
  let (reader, writer) ← E.pipe (O_CLOEXEC ())
  let plan : Plan := {
    uid := uid.toNat
    gid := gid.toNat
    groups := groups.map UInt32.toNat
    path := path
    args := #[path.splitOn "/" |>.getLast!] ++ args
    descriptor := reader.toNat }
  let child ← try Helper.spawn "pam-mail" (toJson plan) #[reader]
    catch error => quietClose writer; throw error
    finally quietClose reader
  let signals ← try E.signalFd ((1 : UInt64) <<< ((SIGPIPE ()).toUInt64 - 1)) catch _ =>
    quietClose writer
    let _ ← E.kill child (SIGKILL ())
    let _ ← wait child
    throw (IO.userError "unable to protect mail pipe")
  try E.writeAll writer body.toUTF8 catch _ => pure ()
    finally quietClose writer
  try let _ ← E.readSignal signals catch _ => pure ()
  quietClose signals
  let _ ← wait child

end LeanSudo.Sys.PamHelpers
