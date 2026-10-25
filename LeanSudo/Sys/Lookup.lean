import LeanSudo.Sys.Core
import LeanSudo.Helper
import LeanSudo.Sys.Prim.Lookup

namespace LeanSudo.Sys.Lookup

namespace platform
export Prim.Lookup (missing notDirectory denied notPermitted loop invalid io
  interrupted kill intMax execBits)
end platform

def executable (st : FileStat) : Bool :=
  st.isReg && (st.mode &&& (platform.execBits ()).toNat) != 0

theorem executable_iff (st : FileStat) :
    executable st = true ↔
      st.isReg = true ∧ (st.mode &&& (platform.execBits ()).toNat) != 0 := by
  simp [executable]

open Lean

def unavailable (error : Nat) : Bool :=
  error == (platform.missing ()).toNat || error == (platform.notDirectory ()).toNat ||
    error == (platform.denied ()).toNat || error == (platform.notPermitted ()).toNat ||
    error == (platform.loop ()).toNat

theorem unavailable_iff (error : Nat) :
    unavailable error = true ↔
      error = (platform.missing ()).toNat ∨ error = (platform.notDirectory ()).toNat ∨
      error = (platform.denied ()).toNat ∨ error = (platform.notPermitted ()).toNat ∨
      error = (platform.loop ()).toNat := by
  simp [unavailable, or_assoc]

def helperName : String := "lookup-paths"

private structure Plan where
  paths : Array String
  uid : Nat
  gid : Nat
  groups : Array Nat
  descriptor : Nat
  deriving ToJson, FromJson

private def validPlan (plan : Plan) : Bool :=
  plan.uid < UInt32.size - 1 && plan.gid < UInt32.size - 1 &&
    plan.groups.all (· < UInt32.size - 1) &&
    plan.paths.size ≤ 65536 && plan.groups.size ≤ 65536 &&
    plan.paths.all (fun path => !path.contains '\x00') &&
    plan.descriptor ≤ (platform.intMax ()).toNat

private def quietClose (fd : UInt32) : IO Unit := do
  try Prim.Exec.close fd catch _ => pure ()

private def encodeWords (words : Array UInt64) : ByteArray := Id.run do
  let mut bytes := ByteArray.emptyWithCapacity (words.size * 8)
  for word in words do
    for shift in [:8] do
      bytes := bytes.push ((word >>> (shift * 8).toUInt64).toUInt8)
  return bytes

private def decodeWord (bytes : ByteArray) (offset : Nat) : UInt64 := Id.run do
  let mut word : UInt64 := 0
  for shift in [:8] do
    word := word ||| (bytes[offset + shift]!.toUInt64 <<< (shift * 8).toUInt64)
  return word

private partial def statPath (path : String) : IO (Int × Array Int) := do
  let result ← Prim.CoreFacts.stat path
  if result.1 == -((platform.interrupted ()).toNat : Int) then return ← statPath path
  return result

private def helper (json : Json) : IO UInt32 := do
  let plan ← IO.ofExcept (fromJson? json : Except String Plan)
  unless validPlan plan do Prim.CoreFacts.failErrno (platform.invalid ()).toNat
  let fd := plan.descriptor.toUInt32
  try
    let error ← try
      Helper.dropCredentials plan.uid.toUInt32 plan.gid.toUInt32
        (plan.groups.map Nat.toUInt32)
      pure none
    catch error => pure (some error.toString)
    if let some error := error then
      let bytes := error.toUTF8
      Prim.Exec.writeAll fd (encodeWords #[bytes.size.toUInt64, plan.paths.size.toUInt64])
      Prim.Exec.writeAll fd bytes
      return 0
    Prim.Exec.writeAll fd (encodeWords #[0, plan.paths.size.toUInt64])
    for path in plan.paths do
      let (rc, fields) ← statPath path
      let words := if rc < 0 then
          #[rc.natAbs.toUInt64, 0, 0, 0, 0, 0, 0, 0]
        else
          #[0, fields[0]!.toNat.toUInt64, fields[1]!.toNat.toUInt64,
            fields[2]!.toNat.toUInt64, fields[3]!.toNat.toUInt64,
            fields[4]!.toNat.toUInt64, fields[5]!.toNat.toUInt64,
            fields[6]!.toNat.toUInt64]
      Prim.Exec.writeAll fd (encodeWords words)
    return 0
  finally quietClose fd

def register : IO Unit :=
  Helper.register helperName helper

private partial def readExactly (fd : UInt32) (size : Nat)
    (bytes : ByteArray := ByteArray.empty) : IO ByteArray := do
  if bytes.size == size then return bytes
  let (error, chunk) ← Prim.Exec.read fd (size - bytes.size).toUInt32
  if error == platform.interrupted () then return ← readExactly fd size bytes
  if error != 0 then Prim.CoreFacts.failErrno error.toNat
  if chunk.isEmpty || bytes.size + chunk.size > size then
    Prim.CoreFacts.failErrno (platform.io ()).toNat
  readExactly fd size (bytes ++ chunk)

private partial def checkEof (fd : UInt32) : IO Unit := do
  let (error, bytes) ← Prim.Exec.read fd 1
  if error == platform.interrupted () then return ← checkEof fd
  if error != 0 then Prim.CoreFacts.failErrno error.toNat
  unless bytes.isEmpty do Prim.CoreFacts.failErrno (platform.io ()).toNat

private partial def waitChild (pid : UInt32) : IO Unit := do
  let (result, status) ← Prim.Exec.waitpid pid 0
  if result.toInt == -((platform.interrupted ()).toNat : Int) then return ← waitChild pid
  if result < 0 then Prim.CoreFacts.failErrno (-result).toInt
  if result.toInt.toNat != pid.toNat || status != 0 then
    Prim.CoreFacts.failErrno (platform.io ()).toNat

private def readReply (fd : UInt32) (count : Nat) :
    IO (Array (Option FileStat) × Option String) := do
  let header ← readExactly fd 16
  let errorSize := (decodeWord header 0).toNat
  unless (decodeWord header 8).toNat == count && errorSize ≤ 65536 do
    Prim.CoreFacts.failErrno (platform.io ()).toNat
  if errorSize != 0 then
    let bytes ← readExactly fd errorSize
    let some error := String.fromUTF8? bytes | Prim.CoreFacts.failErrno (platform.io ()).toNat
    checkEof fd
    return (#[], some error)
  let mut facts := Array.emptyWithCapacity count
  let mut failure : Option String := none
  for _ in [:count] do
    let bytes ← readExactly fd 64
    let error := (decodeWord bytes 0).toNat
    if error != 0 then
      if !unavailable error && failure.isNone then
        failure := some (← Prim.CoreFacts.strerror
          (if error ≤ (platform.intMax ()).toNat then error.toUInt32 else platform.io ()))
      facts := facts.push none
    else
      facts := facts.push (some {
        dev := (decodeWord bytes 8).toNat
        ino := (decodeWord bytes 16).toNat
        mode := (decodeWord bytes 24).toNat
        uid := (decodeWord bytes 32).toNat
        gid := (decodeWord bytes 40).toNat
        size := (decodeWord bytes 48).toNat
        rdev := (decodeWord bytes 56).toNat })
  checkEof fd
  return (facts, failure)

def inspectPaths (paths : Array String) (uid gid : Nat) (groups : Array Nat) :
    IO (Array (Option FileStat)) := do
  if uid ≥ UInt32.size - 1 || gid ≥ UInt32.size - 1 ||
      groups.any (· ≥ UInt32.size - 1) then
    throw (IO.userError "command lookup: uid or gid out of range")
  if paths.size > 65536 || groups.size > 65536 ||
      paths.any (·.contains '\x00') then
    Prim.CoreFacts.failErrno (platform.invalid ()).toNat
  let (reader, writer) ← Prim.Exec.pipe
  try
    let plan : Plan := { paths, uid, gid, groups, descriptor := writer.toNat }
    let child ← try Helper.spawn helperName (toJson plan) #[writer]
      finally quietClose writer
    let reply ← try readReply reader paths.size
      catch error =>
        discard <| Prim.Exec.kill child (platform.kill ())
        try waitChild child catch _ => pure ()
        throw error
    let exitError ← try waitChild child; pure none
      catch error => pure (some error)
    if let some error := reply.2 then throw (IO.userError error)
    if let some error := exitError then throw error
    return reply.1
  finally
    quietClose reader

end LeanSudo.Sys.Lookup
