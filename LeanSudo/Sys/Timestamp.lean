import LeanSudo.Timestamp

/-!
# Timestamp storage, boot clock and process identity (IO)

Backed by `c/ts.c`. The timestamp directory is fixed at compile time
(`timestampBaseDir`); there is deliberately no environment override.
-/

namespace LeanSudo.Sys

/-- Root of lean-sudo's runtime state. Records live in `<base>/ts/<uid>`. -/
def timestampBaseDir : String := "/run/lean-sudo"

/-- `CLOCK_BOOTTIME` in nanoseconds (keeps counting during suspend). -/
@[extern "lean_sudo_ts_boottime"]
opaque bootTimeNanos : IO Nat

@[extern "lean_sudo_ts_getsid"]
private opaque getsidRaw : IO UInt32

@[extern "lean_sudo_ts_getppid"]
private opaque getppidRaw : IO UInt32

/-- Session id of the calling process (`getsid(0)`). -/
def getsid : IO Nat := return (← getsidRaw).toNat

/-- Parent process id. -/
def getppid : IO Nat := return (← getppidRaw).toNat

/-- Raw bytes of `/proc/<pid>/stat`, or `none` if unreadable. -/
private def readProcStat (pid : String) : IO (Option (List UInt8)) := do
  try
    let b ← IO.FS.readBinFile s!"/proc/{pid}/stat"
    return some b.data.toList
  catch _ => return none

/-- Start time of process `pid` in clock ticks since boot (`/proc/<pid>/stat`
field 22), or `none` if the process does not exist / cannot be parsed. -/
def processStartTime (pid : Nat) : IO (Option Nat) := do
  let some bs ← readProcStat (toString pid) | return none
  return Timestamp.statField bs 22

/-- Device number (`st_rdev`) of the controlling terminal of this process, or `none`
when there is none. Like sudo on Linux this uses the kernel's view
(`/proc/self/stat` field 7, `tty_nr`), so redirected std fds cannot select a
different terminal. -/
def ttyDevice : IO (Option Nat) := do
  let some bs ← readProcStat "self" | return none
  match Timestamp.statField bs 7 with
  | some n => return if n == 0 then none else some (Timestamp.ttyNrToDev n)
  | none => return none

@[extern "lean_sudo_ts_open"]
private opaque tsOpen (base : @& String) (uid : UInt32) : IO UInt32

@[extern "lean_sudo_ts_read"]
private opaque tsRead (fd : UInt32) : IO ByteArray

@[extern "lean_sudo_ts_write"]
private opaque tsWrite (fd : UInt32) (bytes : @& ByteArray) : IO Unit

@[extern "lean_sudo_ts_close"]
private opaque tsClose (fd : UInt32) : IO Unit

@[extern "lean_sudo_ts_remove"]
private opaque tsRemove (base : @& String) (uid : UInt32) : IO Unit

private def uidToUInt32 (uid : Nat) : IO UInt32 :=
  if uid < UInt32.size then return uid.toUInt32
  else throw (IO.userError s!"timestamp: uid {uid} out of range")

/-- Open `<base>/ts/<uid>` (creating `<base>` 0711 and `<base>/ts` 0700 if missing;
both must be root-owned real directories that are not group/world writable; the file
is opened `O_NOFOLLOW`, 0600, and must be a root-owned regular file with one link),
take an exclusive `flock`, pass the contents (at most 64 KiB, larger files read as
empty) to `f`, and replace the contents with its result if `some`. Fails with an
`IO.userError` when not running with euid 0. -/
def withTimestampFile (uid : Nat) (f : ByteArray → IO (Option ByteArray × α)) : IO α := do
  let u ← uidToUInt32 uid
  let fd ← tsOpen timestampBaseDir u
  try
    let contents ← tsRead fd
    let (out, a) ← f contents
    if let some bytes := out then tsWrite fd bytes
    return a
  finally
    tsClose fd

/-- `sudo -K`: remove `<base>/ts/<uid>`; a missing file is not an error. -/
def removeTimestampFile (uid : Nat) : IO Unit := do
  tsRemove timestampBaseDir (← uidToUInt32 uid)

end LeanSudo.Sys
