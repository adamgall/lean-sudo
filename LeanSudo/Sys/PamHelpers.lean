import LeanSudo.Helper
import LeanSudo.Sys.Prim.Pam

namespace LeanSudo.Sys.PamHelpers

open Lean Prim.Posix
open Prim.Pam (errorCode invalidFd)
namespace E
export Prim.Exec (pipe close dup2 openFile closeRange signalMask waitpid kill getuid getgid
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
  deriving ToJson, FromJson

private def validPlan (plan : Plan) : Bool :=
  plan.uid < UInt32.size - 1 && plan.gid < UInt32.size - 1 &&
    plan.groups.all (· < UInt32.size - 1) && plan.descriptor ≤ (INT_MAX ()).toNat &&
    !plan.path.contains '\x00' && plan.args.all (fun value => !value.contains '\x00') &&
    plan.prompt.all (fun byte => byte > 0 && byte < 256)

private def decode (json : Json) : IO Plan := do
  let plan ← IO.ofExcept (fromJson? json)
  unless validPlan plan do throw (IO.userError "invalid helper plan")
  return plan

private def drop (plan : Plan) : IO Unit :=
  Helper.dropCredentials plan.uid.toUInt32 plan.gid.toUInt32 (plan.groups.map Nat.toUInt32)

private def openNull (flags : UInt32) : IO UInt32 := do
  let fd ← E.openFile "/dev/null" flags 0
  if fd < 0 then throw (IO.userError "unable to open /dev/null")
  return fd.toInt.toNat.toUInt32

private def execPlan (plan : Plan) : IO UInt32 := do
  if (← E.closeRange (STDERR_FILENO () + 1) (invalidFd ()) 0) != 0 then return 126
  E.signalMask (← Helper.inheritedMask)
  let _ ← withArgv (plan.args.map String.toUTF8) (execInherited plan.path)
  return 127

private def askpassChild (json : Json) : IO UInt32 := do
  let plan ← decode json
  try
    E.dup2 plan.descriptor.toUInt32 (STDOUT_FILENO ())
    E.dup2 (← openNull (O_RDONLY ())) (STDIN_FILENO ())
    drop plan
    if (← E.closeRange (STDERR_FILENO () + 1) (invalidFd ()) 0) != 0 then return 126
    E.signalMask (← Helper.inheritedMask)
    let args := #[plan.path.toUTF8, ByteArray.mk (plan.prompt.map Nat.toUInt8)]
    let _ ← withArgv args (execInherited plan.path)
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
  let ready ← Prim.Pam.poll fd (invalidFd ()) timeout
  if ready == errorCode (EINTR ()) then return ← askpassLoop fd deadline bytes
  if ready == 0 then return (3, ByteArray.empty)
  if ready < 0 then return (5, ByteArray.empty)
  let (count, input) ← Prim.Pam.read fd 1
  if count == errorCode (EINTR ()) then return ← askpassLoop fd deadline bytes
  if count < 0 then return (5, ByteArray.empty)
  if count == 0 || input[0]! == 10 then
    return (if bytes.isEmpty then 4 else 0, bytes)
  askpassLoop fd deadline (if bytes.size < 1023 then bytes.push input[0]! else bytes)

def readAskpass (path : String) (prompt : ByteArray) (uid gid : UInt32)
    (groups : Array UInt32) (timeout : UInt32) : IO (Int × ByteArray) := do
  let descriptors ← try pure (some (← E.pipe (O_CLOEXEC ()))) catch _ => pure none
  let some (reader, writer) := descriptors | return (5, ByteArray.empty)
  let plan : Plan := {
    uid := uid.toNat
    gid := gid.toNat
    groups := groups.map UInt32.toNat
    path := path
    prompt := prompt.data.map UInt8.toNat
    descriptor := writer.toNat }
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
  unless validPlan plan do throw (IO.userError "invalid admin flag arguments")
  let child ← Helper.spawn "pam-admin" (toJson plan)
  if (← wait child) != 0 then throw (IO.userError "unable to create admin flag")

def sendMail (path : String) (args : Array String) (body : String) : IO Unit := do
  if path.contains '\x00' || body.contains '\x00' || args.any (·.contains '\x00') then
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
