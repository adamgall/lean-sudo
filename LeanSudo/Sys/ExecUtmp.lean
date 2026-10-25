import LeanSudo.Sys.ExecRelay
import LeanSudo.Sys.Prim.CoreFacts

namespace LeanSudo.Sys.Exec

open Prim.Exec

private def putBytes (record : ByteArray) (offset width : Nat) (bytes : ByteArray) : ByteArray :=
  Id.run do
    let mut record := record
    for i in [:width] do record := record.set! (offset + i) (bytes[i]?.getD 0)
    return record

private def putWord (record : ByteArray) (offset width : Nat) (value : UInt32) : ByteArray :=
  Id.run do
    let mut record := record
    for i in [:width] do
      let shift := if K.littleEndian () != 0 then i else width - 1 - i
      record := record.set! (offset + i) (value.toUInt64 >>> (shift * 8).toUInt64).toUInt8
    return record

private def ttyLine (fd : UInt32) : IO (Option ByteArray) := do
  let some bytes ← Prim.CoreFacts.ttyname fd | return none
  let some name := String.fromUTF8? bytes | return none
  let line := if name.startsWith "/dev/" then String.ofList (name.toList.drop 5) else name
  return some line.toUTF8

def beginUtmp (pty : Pty) (user : Option String) : IO (Option ByteArray) := do
  let some user := user | return none
  let some line ← ttyLine pty.slave | return none
  let mut entry := ByteArray.mk (Array.replicate (K.utmpSize ()) 0)
  Prim.Exec.utmpStart
  try
    if let some oldLine ← ttyLine pty.tty then
      let key := putBytes entry (K.utmpLine ()) (K.utmpLineSize ()) oldLine
      if let some old ← Prim.Exec.utmpGet key then
        if old.size == (K.utmpSize ()) then entry := old
      Prim.Exec.utmpStart
    entry := putBytes entry (K.utmpLine ()) (K.utmpLineSize ()) line
    entry := putBytes entry (K.utmpId ()) (K.utmpIdSize ())
      (line.extract (line.size - (K.utmpIdSize ())) line.size)
    entry := putBytes entry (K.utmpUser ()) (K.utmpUserSize ()) user.toUTF8
    entry := putWord entry (K.utmpType ()) (K.utmpTypeSize ()) (K.USER_PROCESS ())
    entry := putWord entry (K.utmpPid ()) (K.utmpPidSize ()) (← Prim.Exec.getpid)
    entry := putWord entry (K.utmpSeconds ()) (K.utmpSecondsSize ())
      (← Prim.Exec.unixTime).toUInt32
    entry := putWord entry (K.utmpMicros ()) (K.utmpMicrosSize ()) 0
    if ← Prim.Exec.utmpPut entry then return some entry
    return none
  finally Prim.Exec.utmpEnd

def finishUtmp (entry : ByteArray) (status : UInt32) : IO Unit := do
  let entry := putBytes entry (K.utmpUser ()) (K.utmpUserSize ()) ByteArray.empty
  let entry := putWord entry (K.utmpType ()) (K.utmpTypeSize ()) (K.DEAD_PROCESS ())
  let signal := status &&& (K.waitSignalMask ())
  let entry := putWord entry (K.utmpTermination ()) (K.utmpTerminationSize ()) signal
  let code := if signal == 0 then (status >>> (K.waitShift ())) &&& (K.waitByteMask ()) else 0
  let entry := putWord entry (K.utmpExit ()) (K.utmpExitSize ()) code
  let entry := putWord entry (K.utmpSeconds ()) (K.utmpSecondsSize ())
    (← Prim.Exec.unixTime).toUInt32
  Prim.Exec.utmpStart
  try discard <| Prim.Exec.utmpPut entry finally Prim.Exec.utmpEnd

end LeanSudo.Sys.Exec
