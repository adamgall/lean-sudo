import LeanSudo.Timestamp

/-!
# sudo timestamp storage, clock and process identity

The v2 wire format is pure (`LeanSudo.Timestamp`). This layer implements sudo's
header/record locking protocol; `c/ts.c` only supplies checked file operations.
Records retain their offsets, including foreign records, so POSIX record locks
interoperate with sudo.ws. See sudo 1.9.17p2 `plugins/sudoers/timestamp.c`.
-/

namespace LeanSudo.Sys

structure TimestampConfig where
  directory : String := "/run/sudo/ts"
  uid : Nat
  ownerUid : Nat := 0
  ownerGid : Nat := 0
  deriving Inhabited

structure TimestampKey where
  scope : Timestamp.Scope
  lockScope : Timestamp.Scope
  sid : Nat
  authUid : Nat
  deriving Inhabited

/-- sudo_gettime_mono uses CLOCK_BOOTTIME on Linux. -/
@[extern "lean_sudo_ts_boottime"]
opaque bootTimeNanos : IO Nat

@[extern "lean_sudo_ts_getsid"]
private opaque getsidRaw : IO UInt32
@[extern "lean_sudo_ts_getppid"]
private opaque getppidRaw : IO UInt32
@[extern "lean_sudo_ts_clock_ticks"]
private opaque clockTicks : IO Nat

def getsid : IO Nat := return (← getsidRaw).toNat
def getppid : IO Nat := return (← getppidRaw).toNat

private def readProcStat (pid : String) : IO (Option (List UInt8)) := do
  try
    return some (← IO.FS.readBinFile s!"/proc/{pid}/stat").data.toList
  catch _ => return none

/-- Process birth time as a timespec-compatible nanosecond count, not raw jiffies. -/
def processStartTime (pid : Nat) : IO (Option Nat) := do
  let some bs ← readProcStat (toString pid) | return none
  let some ticks := Timestamp.statField bs 22 | return none
  let frequency ← clockTicks
  if frequency == 0 then throw (IO.userError "invalid clock tick frequency")
  return some (ticks / frequency * 1000000000 + ticks % frequency * 1000000000 / frequency)

/-- The kernel's controlling-terminal device, independent of redirected stdio. -/
def ttyDevice : IO (Option Nat) := do
  let some bs ← readProcStat "self" | return none
  match Timestamp.statField bs 7 with
  | some n => return if n == 0 then none else some (Timestamp.ttyNrToDev n)
  | none => return none

@[extern "lean_sudo_ts_open"]
private opaque tsOpen (directory name : @& String) (uid gid : UInt32) (create : Bool) : IO (Option UInt32)
@[extern "lean_sudo_ts_read"]
private opaque tsRead (fd : UInt32) : IO ByteArray
@[extern "lean_sudo_ts_read_at"]
private opaque tsReadAt (fd : UInt32) (offset : UInt64) (length : UInt32) : IO ByteArray
@[extern "lean_sudo_ts_pwrite"]
private opaque tsWriteAt (fd : UInt32) (offset : UInt64) (bytes : @& ByteArray) : IO Unit
@[extern "lean_sudo_ts_truncate"]
private opaque tsTruncate (fd : UInt32) (length : UInt64) : IO Unit
@[extern "lean_sudo_ts_lock"]
private opaque tsLock (fd : UInt32) (offset length : UInt64) (lock : Bool) : IO Unit
@[extern "lean_sudo_ts_close"]
private opaque tsClose (fd : UInt32) : IO Unit
@[extern "lean_sudo_ts_remove"]
private opaque tsRemove (directory name : @& String) (uid gid : UInt32) : IO Unit

private def uidToUInt32 (uid : Nat) : IO UInt32 :=
  if uid < UInt32.size - 1 then return uid.toUInt32
  else throw (IO.userError s!"timestamp: uid {uid} out of range")

@[extern "lean_sudo_state_marker"]
private opaque stateMarkerRaw (dir : @& String) (uid : UInt32) (create : Bool) : IO Bool

/-- Lecture markers are independent of authentication timestamps. -/
def stateMarker (dir : String) (uid : Nat) (create : Bool) : IO Bool := do
  stateMarkerRaw dir (← uidToUInt32 uid) create

private def openTimestamp (config : TimestampConfig) (create : Bool) : IO (Option UInt32) := do
  let _ ← uidToUInt32 config.uid
  tsOpen config.directory (toString config.uid)
    (← uidToUInt32 config.ownerUid) (← uidToUInt32 config.ownerGid) create

private def lockRecord (fd : UInt32) (offset : Nat) (lock : Bool) : IO Unit := do
  if offset >= UInt64.size then throw (IO.userError "timestamp offset out of range")
  tsLock fd offset.toUInt64 Timestamp.recordSize.toUInt64 lock

private def writeEntry (fd : UInt32) (offset : Nat) (entry : Timestamp.DiskEntry) : IO Unit := do
  if !decide entry.Representable then throw (IO.userError "timestamp record is out of range")
  if offset >= UInt64.size then throw (IO.userError "timestamp offset out of range")
  tsWriteAt fd offset.toUInt64 (Timestamp.encodeEntry entry)

private def headerWord (bytes : ByteArray) (offset : Nat) : Nat :=
  (bytes[offset]?.getD 0).toNat + 256 * (bytes[offset + 1]?.getD 0).toNat

/-- Preserve old lock headers and all subsequent offsets, as timestamp_lock does. -/
private def initializeHeader (fd : UInt32) (bytes : ByteArray) : IO ByteArray := do
  let size := headerWord bytes 2
  let kind := headerWord bytes 4
  if bytes.size >= 40 && kind == 4 && size >= 8 && size <= bytes.size then return bytes
  if bytes.size >= 40 && size == 40 then
    let header := ByteArray.mk #[bytes[0]!, bytes[1]!, 40, 0, 4, 0] ++
      ByteArray.mk (Array.replicate 34 0)
    tsWriteAt fd 0 header
    return header ++ bytes.extract 40 bytes.size
  let header := Timestamp.encodeEntry Timestamp.lockEntry
  tsTruncate fd 0
  tsWriteAt fd 0 header
  return header

private structure Ticket where
  fd : UInt32
  offset : Nat
  key : TimestampKey
  global : Bool

/-- sudo forms a global key by changing its nonglobal lock key's type, retaining
the otherwise-unused start time and device/parent union fields. -/
private def diskEntry (key : TimestampKey) (record : Timestamp.Record) : Timestamp.DiskEntry :=
  let entry := Timestamp.DiskEntry.ofRecord key.sid record
  if record.scope == .global then
    match key.lockScope with
    | .tty dev _ start => { entry with start, key := dev }
    | .ppid pid start => { entry with start, key := pid }
    | .global => entry
  else entry

private def disabledEntry (key : TimestampKey) (scope : Timestamp.Scope) : Timestamp.DiskEntry :=
  diskEntry key { scope, authUid := key.authUid, time := 0, disabled := true }

private def findEntry (bytes : ByteArray) (scope : Timestamp.Scope) (authUid : Nat) :
    Option Timestamp.LocatedEntry :=
  (Timestamp.scan bytes).find? (fun located => located.entry.matches scope authUid)

private def openTicket (config : TimestampConfig) (key : TimestampKey) : IO Ticket := do
  if key.lockScope == .global then throw (IO.userError "timestamp lock scope must be terminal or process")
  let some fd ← openTimestamp config true | throw (IO.userError "unable to open timestamp file")
  try
    lockRecord fd 0 true
    let (offset, lockOffset) ← try
      let mut bytes ← initializeHeader fd (← tsRead fd)
      let lockOffset ← match findEntry bytes key.lockScope key.authUid with
        | some located => pure located.offset
        | none => do
          let offset := bytes.size
          let entry := disabledEntry key key.lockScope
          writeEntry fd offset entry
          bytes := bytes ++ Timestamp.encodeEntry entry
          pure offset
      let offset ← if key.scope == .global then
          match findEntry bytes key.scope key.authUid with
          | some located => pure located.offset
          | none => do
            writeEntry fd bytes.size (disabledEntry key key.scope)
            pure bytes.size
        else pure lockOffset
      pure (offset, lockOffset)
    finally
      lockRecord fd 0 false
    lockRecord fd lockOffset true
    return { fd, offset, key, global := key.scope == .global }
  catch e =>
    tsClose fd
    throw e

private def readTicket (ticket : Ticket) : IO (List Timestamp.Record) := do
  if ticket.global then lockRecord ticket.fd ticket.offset true
  try
    let bytes ← tsReadAt ticket.fd ticket.offset.toUInt64 Timestamp.recordSize.toUInt32
    let some entry := Timestamp.decodeEntry bytes | return []
    if !entry.matches ticket.key.scope ticket.key.authUid then return []
    return (entry.forSession ticket.key.sid).toList
  finally
    if ticket.global then lockRecord ticket.fd ticket.offset false

private def updateTicket (ticket : Ticket) (record : Timestamp.Record) : IO Unit := do
  let entry := diskEntry ticket.key record
  if !entry.matches ticket.key.scope ticket.key.authUid then
    throw (IO.userError "timestamp update does not match locked record")
  if ticket.global then lockRecord ticket.fd ticket.offset true
  try writeEntry ticket.fd ticket.offset entry
  finally
    if ticket.global then lockRecord ticket.fd ticket.offset false

/-- Read a nonblocking policy snapshot without creating a file/record. It is not
an authentication grant: execution always rechecks under the long-held terminal
lock. Descriptors are never simultaneously reopened (fcntl close rule). -/
def readTimestamp (config : TimestampConfig) (key : TimestampKey) : IO (List Timestamp.Record) := do
  let some fd ← openTimestamp config false | return []
  try
    let bytes ← tsRead fd
    if headerWord bytes 4 != 4 then return []
    let some located := findEntry bytes key.scope key.authUid | return []
    return (located.entry.forSession key.sid).toList
  finally tsClose fd

private def reportCacheError (report : String → IO Unit) (error : IO.Error) : IO Unit :=
  match error with
  -- sudo's frontend treats an interrupted record lock as an uncached attempt,
  -- without a cache-IO diagnostic (including inherited ignored dispositions).
  | .interrupted _ _ _ => pure ()
  | _ => report error.toString

/-- Serialize authentication with sudo.ws's per-terminal/process record lock.
Global tickets take a separate short lock only around status/update. Cache IO
errors are reported, then authentication proceeds without trusting a cache;
callback errors are never retried. An update changes only the selected record. -/
def withTimestampFile (config : TimestampConfig) (key : TimestampKey)
    (f : List Timestamp.Record → IO (Option Timestamp.Record × α))
    (report : String → IO Unit := fun _ => pure ()) : IO α := do
  let opened : Except IO.Error Ticket ←
    try pure (.ok (← openTicket config key)) catch e => pure (.error e)
  match opened with
  | .error e =>
    reportCacheError report e
    return (← f []).2
  | .ok ticket =>
    try
      let records ← try readTicket ticket catch e => reportCacheError report e; pure []
      let (record, result) ← f records
      if let some record := record then
        try updateTicket ticket record catch e => reportCacheError report e
      return result
    finally tsClose ticket.fd

/-- `sudo -k`: lock the header and disable matching records for every auth uid.
The removal key intentionally differs from authentication for Linux kernel mode. -/
def invalidateTimestamp (config : TimestampConfig) (scope : Timestamp.Scope) : IO Unit := do
  let some fd ← openTimestamp config false | return
  try
    lockRecord fd 0 true
    let bytes ← tsRead fd
    for located in Timestamp.scan bytes do
      if located.entry.matches scope 0 true then
        writeEntry fd located.offset { located.entry with flags := located.entry.flags ||| 1 }
  finally tsClose fd

/-- `sudo -K`: unlink the invoking UID's timestamp file, if present. -/
def removeTimestampFile (config : TimestampConfig) : IO Unit := do
  let _ ← uidToUInt32 config.uid
  tsRemove config.directory (toString config.uid)
    (← uidToUInt32 config.ownerUid) (← uidToUInt32 config.ownerGid)

end LeanSudo.Sys
