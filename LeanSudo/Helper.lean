import Lean
import Std.Sync.Mutex
import LeanSudo.Sys.Prim.Exec
import LeanSudo.Sys.Prim.CoreFacts

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
  payload : Json
  deriving ToJson, FromJson

def channelAccepted (socket : Bool) (parent pid uid effectiveUid : UInt32) : Bool :=
  socket && decide (1 < parent) && pid == parent && uid == effectiveUid

theorem channelAccepted_iff (socket : Bool) (parent pid uid effectiveUid : UInt32) :
    channelAccepted socket parent pid uid effectiveUid = true ↔
      socket = true ∧ 1 < parent ∧ pid = parent ∧ uid = effectiveUid := by
  simp [channelAccepted, Bool.and_eq_true, and_assoc]

def envelopeAccepted (envelope : Envelope) (parent effectiveUid : Nat) : Bool :=
  envelope.magic == "lean-sudo-helper-1" && envelope.parent == parent &&
    envelope.effectiveUid == effectiveUid && decide (envelope.mask < UInt64.size)

theorem envelopeAccepted_iff (envelope : Envelope) (parent effectiveUid : Nat) :
    envelopeAccepted envelope parent effectiveUid = true ↔
      envelope.magic = "lean-sudo-helper-1" ∧ envelope.parent = parent ∧
      envelope.effectiveUid = effectiveUid ∧ envelope.mask < UInt64.size := by
  simp [envelopeAccepted, Bool.and_eq_true, and_assoc]

theorem authenticatedEnvelope_peer (socket : Bool) (parent pid uid effectiveUid : UInt32)
    (envelope : Envelope)
    (channel : channelAccepted socket parent pid uid effectiveUid = true)
    (message : envelopeAccepted envelope parent.toNat effectiveUid.toNat = true) :
    socket = true ∧ envelope.parent = pid.toNat ∧ envelope.effectiveUid = uid.toNat ∧
      envelope.magic = "lean-sudo-helper-1" ∧ envelope.mask < UInt64.size := by
  obtain ⟨socketOk, _, peerPid, peerUid⟩ :=
    (channelAccepted_iff socket parent pid uid effectiveUid).mp channel
  obtain ⟨magic, envelopePid, envelopeUid, mask⟩ :=
    (envelopeAccepted_iff envelope parent.toNat effectiveUid.toNat).mp message
  exact ⟨socketOk, peerPid ▸ envelopePid, peerUid ▸ envelopeUid, magic, mask⟩

def helperDescriptors (keep : Array UInt32) (channel : UInt32) : Array UInt32 :=
  (keep.filter (· != channel)).push channel

theorem helperDescriptors_exact (keep : Array UInt32) (channel fd : UInt32) :
    fd ∈ helperDescriptors keep channel ↔ fd ∈ keep ∨ fd = channel := by
  simp only [helperDescriptors, Array.mem_push, Array.mem_filter, bne_iff_ne]
  by_cases h : fd = channel <;> simp [h]

theorem helperDescriptors_channel (keep : Array UInt32) (channel : UInt32) :
    channel ∈ helperDescriptors keep channel := by
  simp [helperDescriptors_exact]

def channelDescriptor (value : String) : Option UInt32 :=
  value.toNat?.bind fun fd => if fd ≤ 0x7FFFFFFF then some fd.toUInt32 else none

theorem channelDescriptor_bounded (value : String) (fd : UInt32)
    (h : channelDescriptor value = some fd) : fd.toNat ≤ 0x7FFFFFFF := by
  simp only [channelDescriptor, Option.bind_eq_some_iff] at h
  obtain ⟨n, _, hn⟩ := h
  split at hn
  · rename_i bound
    cases hn
    have exact : n.toUInt32.toNat = n := by
      rw [Nat.toUInt32, UInt32.toNat_ofNat']
      omega
    omega
  · contradiction

def restoredMask (mask : Nat) : UInt64 := mask.toUInt64

theorem restoredMask_exact (mask : Nat) (h : mask < UInt64.size) :
    (restoredMask mask).toNat = mask := by
  simp [restoredMask, Nat.toUInt64, UInt64.toNat_ofNat', Nat.mod_eq_of_lt h]

theorem restoredMask_roundtrip (mask : UInt64) : restoredMask mask.toNat = mask := by
  simp [restoredMask]

private initialize handlers : IO.Ref (Array (String × (Json → IO UInt32))) ← IO.mkRef #[]
private initialize originalMask : IO.Ref (Option UInt64) ← IO.mkRef none
private initialize spawnMutex : Std.Mutex Unit ← Std.Mutex.new ()
private initialize pinnedDescriptor : IO.Ref (Option UInt32) ← IO.mkRef none

def marker : String := "LEAN_SUDO_HELPER"

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

def spawn (name : String) (payload : Json) (keepFds : Array UInt32 := #[])
    (remap : Option (UInt32 × UInt32) := none) : IO UInt32 := do
  spawnMutex.mutex.lock
  try
    let target := (remap.map (·.2)).getD 0xFFFFFFFF
    let owned ← IO.mkRef (#[] : Array UInt32)
    let away (fd : UInt32) : IO UInt32 := do
      if fd != target then return fd
      let moved ← checked (← P.fcntl fd (K.F_DUPFD_CLOEXEC ()) (target + 1))
      owned.modify (·.push moved)
      return moved
    try
      let executable ← away (← binaryDescriptor)
      let (ruid, euid, suid) ← P.getresuid
      if euid != suid then P.threadSetresuid ruid suid suid
      let (lowParent, lowChild) ← try P.socketpair
        finally if euid != suid then
          try P.threadSetresuid ruid euid suid catch _ => IO.Process.exit 1
      owned.modify (·.push lowParent |>.push lowChild)
      let parentEnd ← away lowParent
      let childEnd ← away lowChild
      let envelope : Envelope := {
        magic := "lean-sudo-helper-1"
        parent := (← P.getpid).toNat
        effectiveUid := suid.toNat
        mask := (← inheritedMask).toNat
        name, payload }
      let bytes := (toJson envelope).compress.toUTF8
      if bytes.size > 16 * 1024 * 1024 then throw (IO.userError "helper plan is too large")
      let inherited := helperDescriptors keepFds childEnd
      let (source, target) := remap.getD (0xFFFFFFFF, 0xFFFFFFFF)
      let child ← P.forkHelper executable inherited source target
        s!"{marker}={childEnd.toNat}"
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

private partial def readPlan (channel : UInt32) (bytes : ByteArray := ByteArray.empty) :
    IO ByteArray := do
  let (error, chunk) ← P.read channel 8192
  if error == (K.EINTR ()) then return ← readPlan channel bytes
  if error != 0 then throw (IO.userError (← P.strerror error))
  if chunk.isEmpty then return bytes
  if bytes.size + chunk.size > 16 * 1024 * 1024 then
    throw (IO.userError "helper plan is too large")
  readPlan channel (bytes ++ chunk)

private def authenticatedParent (channel : UInt32) : IO Bool := do
  try
    let facts ← P.fstat channel
    let socket := facts[2]! &&& (K.S_IFMT ()) == (K.S_IFSOCK ())
    let parent ← P.getppid
    let (pid, uid, _) ← P.peerCredentials channel
    return channelAccepted socket parent pid uid (← P.geteuid)
  catch _ => return false

def dispatch : IO (Option UInt32) := do
  discard <| binaryDescriptor
  let some value ← IO.getEnv marker | return none
  let some channel := channelDescriptor value | return none
  unless ← authenticatedParent channel do return none
  discard <| Sys.Prim.CoreFacts.unsetenv marker
  try
    let bytes ← try readPlan channel finally ignoreClose channel
    let some text := String.fromUTF8? bytes | return some 127
    let .ok json := Json.parse text | return some 127
    let .ok envelope := (fromJson? json : Except String Envelope) | return some 127
    unless envelopeAccepted envelope (← P.getppid).toNat (← P.geteuid).toNat do return some 127
    originalMask.set (some (restoredMask envelope.mask))
    let some (_, handler) := (← handlers.get).find? (fun entry => entry.1 == envelope.name)
      | return some 127
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

theorem verified_exact (plan : Credentials) (actual : Verification) :
    verified plan actual = true ↔
      actual.uids = (plan.ruid, plan.uid, plan.uid) ∧
      actual.gids = (plan.gid, plan.gid, plan.gid) ∧
      actual.fsuid = plan.uid ∧ actual.fsgid = plan.gid ∧
      groupsEqual plan.groups actual.groups = true ∧
      actual.regainedUid = false ∧ actual.regainedGid = false := by
  simp [verified, Bool.and_eq_true, and_assoc]

theorem groupsEqual_multiset (left right : Array UInt32) (h : groupsEqual left right = true) :
    left.toList.Perm right.toList := by
  have equality : left.toList.mergeSort (fun a b => a.toNat <= b.toNat) =
      right.toList.mergeSort (fun a b => a.toNat <= b.toNat) := by
    simpa [groupsEqual] using h
  have leftPerm := List.mergeSort_perm left.toList (fun a b => a.toNat <= b.toNat)
  rw [equality] at leftPerm
  exact leftPerm.symm.trans (List.mergeSort_perm _ _)

def credentialsAccepted (plan : Credentials) (actual : Verification) : Bool :=
  (authorize plan actual).isSome

theorem credentialsAccepted_exact (plan : Credentials) (actual : Verification) :
    credentialsAccepted plan actual = true ↔ verified plan actual = true := by
  simp [credentialsAccepted, authorize]

theorem credentialsAccepted_secure (plan : Credentials)
    (actual : Verification) (h : credentialsAccepted plan actual = true) :
    actual.uids = (plan.ruid, plan.uid, plan.uid) ∧
    actual.gids = (plan.gid, plan.gid, plan.gid) ∧
    actual.fsuid = plan.uid ∧ actual.fsgid = plan.gid ∧
    plan.groups.toList.Perm actual.groups.toList ∧
    actual.regainedUid = false ∧ actual.regainedGid = false := by
  obtain ⟨uids, gids, fsuid, fsgid, groups, uid, gid⟩ :=
    (verified_exact plan actual).mp ((credentialsAccepted_exact plan actual).mp h)
  exact ⟨uids, gids, fsuid, fsgid, groupsEqual_multiset _ _ groups, uid, gid⟩

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
  unless credentialsAccepted plan actual do
    mismatch "unable to drop privileges: verification failed"

end LeanSudo.Helper
