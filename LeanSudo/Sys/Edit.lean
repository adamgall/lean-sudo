import LeanSudo.Sys.Exec

namespace LeanSudo.Sys.Edit

def noneFd : UInt32 := 0xFFFFFFFF

structure Identity where
  uid : UInt32
  gid : UInt32
  groups : Array UInt32

def identity (uid gid : Nat) (groups : List Nat) : IO Identity := do
  let some u := Exec.toId? uid | throw (IO.userError "invalid edit uid")
  let some g := Exec.toId? gid | throw (IO.userError "invalid edit gid")
  let gs ← groups.toArray.mapM fun n => match Exec.toId? n with
    | some v => pure v
    | none => throw (IO.userError "invalid edit group")
  pure ⟨u, g, gs⟩

structure Result where
  name : String
  value : UInt32

@[extern "leansudo_edit_op"]
private opaque opRaw (op dir : UInt32) (path : @& String) (uid gid : UInt32)
    (groups : @& Array UInt32) (mask suffixLen : UInt32) : IO Result

def operation (who : Identity) (op : UInt32) (dir : UInt32 := noneFd)
    (path : String := "") (mask : Nat := 0o022) (suffixLen : Nat := 0) : IO Result := do
  unless Exec.cSafe path && mask ≤ 0o777 && suffixLen < UInt32.size do
    throw (IO.userError "invalid edit path or umask")
  opRaw op dir path who.uid who.gid who.groups mask.toUInt32 suffixLen.toUInt32

@[extern "leansudo_edit_close"]
opaque close (fd : UInt32) : IO Unit
@[extern "leansudo_edit_stat"]
opaque stat (fd : UInt32) : IO (Array Nat)
@[extern "leansudo_edit_read"]
opaque read (fd : UInt32) : IO ByteArray
@[extern "leansudo_edit_write"]
opaque write (fd : UInt32) (bytes original : @& ByteArray) : IO Unit
@[extern "leansudo_edit_times"]
opaque setTimes (fd : UInt32) (seconds nanos : UInt64) : IO Unit
@[extern "leansudo_edit_clock"]
opaque clock : IO UInt64

end LeanSudo.Sys.Edit
