import Lean
import Std.Sync.Mutex
import LeanSudo.Sys.Prim.Exec

namespace LeanSudo.Helper

open Lean
open Sys.Prim.Exec
namespace P
export Sys.Prim.Exec (startupMask strerror close getpid geteuid socketpair peerCredentials
  fcntl dup2 forkHelper binaryFd writeAll kill waitpid read fstat getppid getgroups
  setgroups setresgid setresuid threadSetresuid getresgid getresuid fsuid fsgid setuid setgid)
end P

structure Envelope where
  magic : String
  parent : Nat
  effectiveUid : Nat
  mask : Nat
  name : String
  restore63 : Option Nat := none
  payload : Json
  deriving ToJson, FromJson

private initialize handlers : IO.Ref (Array (String × (Json → IO UInt32))) ← IO.mkRef #[]
private initialize originalMask : IO.Ref (Option UInt64) ← IO.mkRef none
private initialize spawnMutex : Std.Mutex Unit ← Std.Mutex.new ()
private initialize pinnedDescriptor : IO.Ref (Option UInt32) ← IO.mkRef none

def register (name : String) (handler : Json → IO UInt32) : IO Unit :=
  handlers.modify fun entries => (entries.filter fun entry => entry.1 != name).push (name, handler)

def inheritedMask : IO UInt64 := do
  match ← originalMask.get with
  | some mask => return mask
  | none => P.startupMask

private def checked (result : Int64) : IO UInt32 := do
  if result < 0 then
    throw (IO.userError (← P.strerror (-result).toInt.toNat.toUInt32))
  return result.toInt.toNat.toUInt32

private def ignoreClose (fd : UInt32) : IO Unit := do
  try P.close fd catch _ => pure ()

def binaryDescriptor : IO UInt32 := do
  if let some descriptor ← pinnedDescriptor.get then return descriptor
  let initial ← P.binaryFd
  let descriptor ← if initial < 3 then
      let relocated ← checked (← P.fcntl initial (K.F_DUPFD_CLOEXEC ()) 3)
      P.close initial
      pure relocated
    else pure initial
  pinnedDescriptor.set (some descriptor)
  return descriptor

def spawn (name : String) (payload : Json) (keepFds : Array UInt32 := #[]) : IO UInt32 := do
  spawnMutex.mutex.lock
  try
    let flags63 ← P.fcntl 63 (K.F_GETFD ()) 0
    if flags63 < 0 && flags63 != -(Int64.ofInt (K.EBADF ()).toNat) then discard <| checked flags63
    let preserve63 := flags63 >= 0 &&
      (keepFds.contains 63 || flags63.toInt.toNat.toUInt32 &&& K.FD_CLOEXEC () == 0)
    let owned ← IO.mkRef (#[] : Array UInt32)
    try
      let executable ← checked (← P.fcntl (← binaryDescriptor) (K.F_DUPFD_CLOEXEC ()) 128)
      owned.modify (·.push executable)
      let saved ← if preserve63 then
          let fd ← checked (← P.fcntl 63 (K.F_DUPFD_CLOEXEC ()) 128)
          owned.modify (·.push fd)
          pure (some fd)
        else pure none
      let (ruid, euid, suid) ← P.getresuid
      if euid != suid then P.threadSetresuid ruid suid suid
      let (lowParent, lowChild) ← try P.socketpair
        finally if euid != suid then
          try P.threadSetresuid ruid euid suid catch _ => IO.Process.exit 1
      let parentEnd ← try checked (← P.fcntl lowParent (K.F_DUPFD_CLOEXEC ()) 128)
        catch error =>
          ignoreClose lowChild
          throw error
        finally ignoreClose lowParent
      owned.modify (·.push parentEnd)
      let childEnd ← try checked (← P.fcntl lowChild (K.F_DUPFD_CLOEXEC ()) 128)
        finally ignoreClose lowChild
      owned.modify (·.push childEnd)
      let envelope : Envelope := {
        magic := "lean-sudo-helper-1"
        parent := (← P.getpid).toNat
        effectiveUid := suid.toNat
        mask := (← inheritedMask).toNat
        name, payload, restore63 := saved.map (·.toNat) }
      let bytes := (toJson envelope).compress.toUTF8
      if bytes.size > 16 * 1024 * 1024 then throw (IO.userError "helper plan is too large")
      let inherited := (keepFds.filter (· != 63)) ++ saved.toArray
      let child ← P.forkHelper executable childEnd inherited
      try
        P.writeAll parentEnd bytes
      catch error =>
        discard <| P.kill child (K.SIGKILL ())
        discard <| P.waitpid child 0
        throw error
      return child
    finally
      for fd in (← owned.get) do ignoreClose fd
  finally spawnMutex.mutex.unlock

private partial def readPlan (bytes : ByteArray := ByteArray.empty) : IO ByteArray := do
  let (error, chunk) ← P.read 63 8192
  if error == (K.EINTR ()) then return ← readPlan bytes
  if error != 0 then throw (IO.userError (← P.strerror error))
  if chunk.isEmpty then return bytes
  if bytes.size + chunk.size > 16 * 1024 * 1024 then
    throw (IO.userError "helper plan is too large")
  readPlan (bytes ++ chunk)

private def authenticatedParent : IO Bool := do
  try
    let channel ← P.fstat 63
    unless channel[2]! &&& (K.S_IFMT ()) == (K.S_IFSOCK ()) do return false
    let parent ← P.getppid
    if parent <= 1 then return false
    let (pid, uid, _) ← P.peerCredentials 63
    return pid == parent && uid == (← P.geteuid)
  catch _ => return false

def dispatch (args : List String) : IO (Option UInt32) := do
  discard <| binaryDescriptor
  unless args == ["--lean-sudo-helper"] do return none
  unless ← authenticatedParent do return none
  try
    let bytes ← readPlan
    P.close 63
    let some text := String.fromUTF8? bytes | return none
    let .ok json := Json.parse text | return none
    let .ok envelope := (fromJson? json : Except String Envelope) | return none
    unless envelope.magic == "lean-sudo-helper-1" &&
        envelope.parent == (← P.getppid).toNat &&
        envelope.effectiveUid == (← P.geteuid).toNat &&
        envelope.mask < UInt64.size do return none
    if let some fd := envelope.restore63 then
      unless 128 ≤ fd && fd ≤ 0x7FFFFFFF do return none
      P.dup2 fd.toUInt32 63
      P.close fd.toUInt32
    originalMask.set (some envelope.mask.toUInt64)
    let some (_, handler) := (← handlers.get).find? (fun entry => entry.1 == envelope.name)
      | return none
    return some (← handler envelope.payload)
  catch _ => return some 127

structure Credentials where
  uid : UInt32
  gid : UInt32
  groups : Array UInt32
  ruid : UInt32
  deriving Repr, BEq

structure Verification where
  uids : UInt32 × UInt32 × UInt32
  gids : UInt32 × UInt32 × UInt32
  fsuid : UInt32
  fsgid : UInt32
  groups : Array UInt32
  regainedUid : Bool
  regainedGid : Bool
  deriving Repr

def groupsEqual (left right : Array UInt32) : Bool :=
  left.toList.mergeSort (fun a b => a.toNat <= b.toNat) ==
    right.toList.mergeSort (fun a b => a.toNat <= b.toNat)

def verified (plan : Credentials) (actual : Verification) : Bool :=
  actual.uids == (plan.ruid, plan.uid, plan.uid) &&
  actual.gids == (plan.gid, plan.gid, plan.gid) &&
  actual.fsuid == plan.uid && actual.fsgid == plan.gid &&
  groupsEqual plan.groups actual.groups && !actual.regainedUid && !actual.regainedGid

def authorize (plan : Credentials) (actual : Verification) : Option Credentials :=
  if verified plan actual then some plan else none

theorem authorize_requires_verification (plan : Credentials) (actual : Verification)
    (result : Credentials) (h : authorize plan actual = some result) :
    verified plan actual = true ∧ result = plan := by
  unfold authorize at h
  split at h
  · simp_all
  · contradiction

def dropCredentials (uid gid : UInt32) (groups : Array UInt32)
    (ruid : Option UInt32 := none) (contextual : Bool := false)
    (threadOnly : Bool := false) : IO Unit := do
  let plan : Credentials := { uid, gid, groups, ruid := ruid.getD uid }
  let operation := fun (message : String) (action : IO Unit) => do
    try action catch error =>
      if contextual then throw (IO.userError s!"{message}: {error}") else throw error
  let mismatch := fun (message : String) => do
    let text ← if contextual then pure message else P.strerror (K.EPERM ())
    throw (IO.userError text)
  let setGroups := if threadOnly then threadSetgroups else P.setgroups
  let setGids := if threadOnly then threadSetresgid else P.setresgid
  let setUids := if threadOnly then P.threadSetresuid else P.setresuid
  let setUid := if threadOnly then threadSetuid else P.setuid
  let setGid := if threadOnly then threadSetgid else P.setgid
  if !contextual || !(groupsEqual groups (← P.getgroups)) then
    operation "unable to set supplementary group IDs" (setGroups groups)
  operation s!"unable to set gid to {gid}" (setGids gid gid gid)
  operation s!"unable to set uid to {uid}" (setUids plan.ruid uid uid)
  let gids ← P.getresgid
  if gids != (gid, gid, gid) then
    mismatch s!"unable to change to runas gid ({gids.1}, {gids.2.1})"
  let uids ← P.getresuid
  if uids != (plan.ruid, uid, uid) then
    mismatch s!"unable to change to runas uid ({uids.1}, {uids.2.1})"
  let actualGroups ← P.getgroups
  unless groupsEqual groups actualGroups do
    mismatch "unable to set supplementary group IDs: verification failed"
  let fsuid ← P.fsuid
  let fsgid ← P.fsgid
  let regainedUid ← if uid != 0 && plan.ruid != 0 then
      (do pure ((← setUid 0) == 0))
    else pure false
  if regainedUid then mismatch "unable to drop privileges: uid 0 could be regained"
  let regainedGid ← if uid != 0 && gid != 0 then
      (do pure ((← setGid 0) == 0))
    else pure false
  if regainedGid then mismatch "unable to drop privileges: gid 0 could be regained"
  let actual : Verification := {
    uids, gids, fsuid, fsgid, groups := actualGroups, regainedUid, regainedGid }
  unless (authorize plan actual).isSome do
    mismatch "unable to drop privileges: verification failed"

end LeanSudo.Helper
