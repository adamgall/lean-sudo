import LeanSudo.EventLog
import LeanSudo.Sys.Prim.CoreLogs
import LeanSudo.Sys.Prim.Exec
import LeanSudo.Sys.Prim.Extra
import LeanSudo.Sys.Prim.Posix
import LeanSudo.Sys.TimeFormat

namespace LeanSudo.Sys.CoreLogs

open Prim.Posix Prim.CoreLogs

private def fail (message : String) : IO α := throw (IO.userError message)

private def errno (error : UInt32) : IO α := do
  fail (← Prim.CoreLogs.strerror error)

private def checked (result : Int) : IO Nat := do
  if result < 0 then errno (-result).toNat.toUInt32 else pure result.toNat

private def checkString (value : String) : IO Unit := do
  if value.contains '\x00' then fail "argument contains a NUL byte"

private def facilityValue (name : String) : IO UInt32 :=
  match name with
  | "authpriv" => pure (LOG_AUTHPRIV ())
  | "auth" => pure (LOG_AUTH ())
  | "daemon" => pure (LOG_DAEMON ())
  | "user" => pure (LOG_USER ())
  | "local0" => pure (LOG_LOCAL0 ())
  | "local1" => pure (LOG_LOCAL1 ())
  | "local2" => pure (LOG_LOCAL2 ())
  | "local3" => pure (LOG_LOCAL3 ())
  | "local4" => pure (LOG_LOCAL4 ())
  | "local5" => pure (LOG_LOCAL5 ())
  | "local6" => pure (LOG_LOCAL6 ())
  | "local7" => pure (LOG_LOCAL7 ())
  | _ => fail "unknown syslog facility"

private def priorityValue (name : String) : IO UInt32 :=
  match name with
  | "alert" => pure (LOG_ALERT ())
  | "crit" => pure (LOG_CRIT ())
  | "err" => pure (LOG_ERR ())
  | "warning" => pure (LOG_WARNING ())
  | "notice" => pure (LOG_NOTICE ())
  | "info" => pure (LOG_INFO ())
  | "debug" => pure (LOG_DEBUG ())
  | _ => fail "unknown syslog priority"

private initialize syslogPidOverride : IO.Ref (Option Nat) ← IO.mkRef none

private initialize syslogIdent : IO.Ref String ← IO.mkRef "sudo"

def setSyslogPidOverride (pid : Option Nat) : IO Unit := syslogPidOverride.set pid

private def openSyslog (facility : UInt32) (pid : Bool) : IO Unit := do
  let override ← syslogPidOverride.get
  let ident := if pid then override.map (s!"sudo[{·}]") |>.getD "sudo" else "sudo"
  let options := if pid && override.isNone then LOG_PID () else 0
  Prim.CoreLogs.openlog ident options facility
  syslogIdent.set ident

def syslog (facility priority msg : String) : IO Unit := do
  let fac ← facilityValue facility
  let pri ← priorityValue priority
  openSyslog fac true
  try Prim.CoreLogs.syslogText (fac ||| pri) msg
  finally Prim.CoreLogs.closelog

def syslogBytes (facility priority : String) (msg : ByteArray) (pid : Bool) : IO Unit := do
  let fac ← facilityValue facility
  let pri ← priorityValue priority
  if msg.size > (INT_MAX ()).toNat || msg.data.contains 0 then fail "invalid syslog message"
  openSyslog fac pid
  try Prim.CoreLogs.syslogBytes (fac ||| pri) msg
  finally Prim.CoreLogs.closelog

def unixTime : IO Nat := do
  let (error, seconds) ← Prim.CoreLogs.time
  if seconds.toInt64.toInt < 0 then errno error else pure seconds.toNat

def noNewPrivs : IO Bool := return (← Prim.CoreLogs.prctl) == 1

def terminalColumns (fd : UInt32) : IO Nat := do
  if fd > INT_MAX () then fail "invalid terminal descriptor"
  if let some fields ← Prim.CoreLogs.fstat fd then
    if fields[0]! &&& (S_IFMT ()).toNat == (S_IFIFO ()).toNat then return 0
  let (error, columns, _) ← Prim.CoreLogs.winsize fd
  return if error == 0 && columns != 0 then columns else 80

def localCivilEpoch (civil : Nat) : IO (Option Int) := do
  if civil >= USize.size / 2 then return none
  let some fields ← Prim.CoreLogs.gmtime civil.toUInt64 | return none
  let epoch ← Prim.CoreLogs.mktime (fields.fields.set! 8 (-1))
  return if epoch == -1 then none else some epoch.toInt

def architecture : IO String := do
  let (error, machine) ← Prim.CoreLogs.uname
  if error != 0 then errno error else pure machine

private def localFormat (year : Bool) : String :=
  if year then "%b %e %H:%M:%S %Y" else "%b %e %H:%M:%S"

private def formatTime (format : String) (fields : TimeFields) (error : String) : IO String := do
  let bytes ← TimeFormat.format format fields
  if bytes.isEmpty || bytes.size >= 64 then fail error
  return Prim.CoreLogs.decodeLossyUTF8 bytes

private def formatLocal (seconds : UInt64) (year : Bool) (error : String) : IO String := do
  let some fields ← Prim.CoreLogs.localtime seconds | fail error
  formatTime (localFormat year) fields error

def logTime (year : Bool) (locale : String) : IO String := do
  checkString locale
  Prim.Extra.withLocale locale "unable to initialize logging locale" do
    let (_, seconds) ← Prim.CoreLogs.time
    formatLocal seconds year "unable to format log timestamp"

def eventTime (year : Bool) (locale : String) : IO EventLog.Time := do
  let (error, seconds, nanoseconds) ← Prim.CoreLogs.clock
  if error != 0 then errno error
  checkString locale
  Prim.Extra.withLocale locale "unable to initialize logging locale" do
    let error := "unable to format event timestamp"
    let some fields ← Prim.CoreLogs.gmtime seconds | fail error
    let iso8601 ← formatTime "%Y%m%d%H%M%SZ" fields error
    let localtime ← formatLocal seconds year error
    return { seconds := seconds.toNat, nanoseconds := nanoseconds.toNat, iso8601, localtime }

private partial def randomBytes (bytes : ByteArray := ByteArray.empty) : IO ByteArray := do
  if bytes.size >= 16 then return bytes
  let (error, chunk) ← Prim.CoreLogs.random (16 - bytes.size).toUInt32
  if error == EINTR () then return ← randomBytes bytes
  if error != 0 then errno error
  if chunk.isEmpty then fail "unable to generate event UUID"
  randomBytes (bytes ++ chunk)

def eventUuid : IO String := do
  let bytes ← randomBytes
  let bytes := bytes.set! 7 ((bytes[7]! &&& 0x0f) ||| 0x40)
  let bytes := bytes.set! 8 ((bytes[8]! &&& 0x3f) ||| 0x80)
  let hex := "0123456789abcdef".toList.toArray
  let mut result := ""
  for i in [:16] do
    if i == 5 || i == 7 || i == 9 || i == 11 then result := result.push '-'
    result := result.push hex[(bytes[i]! >>> 4).toNat]!
    result := result.push hex[(bytes[i]! &&& 15).toNat]!
  return result

def terminalSize : IO (Nat × Nat) := do
  let flags := O_RDONLY () ||| O_NOCTTY () ||| O_CLOEXEC () ||| O_NONBLOCK ()
  let descriptor ← Prim.CoreLogs.openFile "/dev/tty" flags 0
  if descriptor < 0 then return (80, 24)
  let fd := descriptor.toNat.toUInt32
  let (_, columns, rows) ← Prim.CoreLogs.winsize fd
  let _ ← Prim.CoreLogs.close fd
  return (if columns == 0 then 80 else columns, if rows == 0 then 24 else rows)

def signalName (signal : UInt32) : IO String := do
  if signal == SIGHUP () then return "HUP"
  if signal == SIGINT () then return "INT"
  if signal == SIGQUIT () then return "QUIT"
  if signal == SIGILL () then return "ILL"
  if signal == SIGTRAP () then return "TRAP"
  if signal == SIGABRT () then return "ABRT"
  if signal == SIGBUS () then return "BUS"
  if signal == SIGFPE () then return "FPE"
  if signal == SIGKILL () then return "KILL"
  if signal == SIGUSR1 () then return "USR1"
  if signal == SIGSEGV () then return "SEGV"
  if signal == SIGUSR2 () then return "USR2"
  if signal == SIGPIPE () then return "PIPE"
  if signal == SIGALRM () then return "ALRM"
  if signal == SIGTERM () then return "TERM"
  if signal == SIGSTKFLT () then return "STKFLT"
  if signal == SIGCHLD () then return "CHLD"
  if signal == SIGCONT () then return "CONT"
  if signal == SIGSTOP () then return "STOP"
  if signal == SIGTSTP () then return "TSTP"
  if signal == SIGTTIN () then return "TTIN"
  if signal == SIGTTOU () then return "TTOU"
  if signal == SIGURG () then return "URG"
  if signal == SIGXCPU () then return "XCPU"
  if signal == SIGXFSZ () then return "XFSZ"
  if signal == SIGVTALRM () then return "VTALRM"
  if signal == SIGPROF () then return "PROF"
  if signal == SIGWINCH () then return "WINCH"
  if signal == SIGIO () then return "IO"
  if signal == SIGPWR () then return "PWR"
  if signal == SIGSYS () then return "SYS"
  let first ← Prim.CoreLogs.rtmin
  if signal == first then return "RTMIN"
  let last ← Prim.CoreLogs.rtmax
  if signal == last then return "RTMAX"
  if signal > first && signal < last then return s!"RTMIN+{signal - first}"
  return toString signal

def logFileSafe (mode uid : Nat) : Bool :=
  decide (mode &&& (S_IFMT ()).toNat = (S_IFREG ()).toNat ∧ uid = 0 ∧
    mode &&& (S_IWGRP () ||| S_IWOTH ()).toNat = 0)

theorem logFileSafe_iff (mode uid : Nat) :
    logFileSafe mode uid = true ↔
      mode &&& (S_IFMT ()).toNat = (S_IFREG ()).toNat ∧ uid = 0 ∧
        mode &&& (S_IWGRP () ||| S_IWOTH ()).toNat = 0 := by
  simp [logFileSafe]

private partial def writeAll (fd : UInt32) (bytes : ByteArray) (offset : Nat := 0) : IO Unit := do
  if offset >= bytes.size then return
  let result ← Prim.CoreLogs.write fd bytes offset.toUSize
  if result == -(Int.ofNat (EINTR ()).toNat) then return ← writeAll fd bytes offset
  let count ← checked result
  if count == 0 then errno (EIO ())
  writeAll fd bytes (offset + count)

private def openAsRoot (path : String) (flags : UInt32) : IO Int := do
  let (rgid, egid, sgid) ← Prim.Exec.getresgid
  let changed ← if egid == 0 then pure false else
    try Prim.Exec.threadSetresgid rgid 0 sgid; pure true catch _ => pure false
  let mask ← Prim.Exec.umask (S_IRWXG () ||| S_IRWXO ())
  try Prim.CoreLogs.openFile path flags (S_IRUSR () ||| S_IWUSR ())
  finally
    discard <| Prim.Exec.umask mask
    if changed then
      try Prim.Exec.threadSetresgid rgid egid sgid catch _ => IO.Process.exit 1

private def append (path text : String) (json : Bool) : IO Unit := do
  checkString path
  checkString text
  let access := if json then O_RDWR () else O_WRONLY () ||| O_APPEND ()
  let flags := access ||| O_CREAT () ||| O_NOFOLLOW () ||| O_CLOEXEC () ||| O_NONBLOCK ()
  let descriptor ← openAsRoot path flags
  if descriptor < 0 then
    let error ← Prim.CoreLogs.strerror (-descriptor).toNat.toUInt32
    let message := s!"unable to open log file {path}: {error}".toUTF8
    fail (Prim.CoreLogs.decodeLossyUTF8 (message.extract 0 1023))
  let fd := descriptor.toNat.toUInt32
  try
    if json then
      if (← Prim.CoreLogs.flock fd (LOCK_EX ())) != 0 then fail "unsafe or inaccessible log file"
    let some fields ← Prim.CoreLogs.fstat fd | fail "unsafe or inaccessible log file"
    unless logFileSafe fields[0]! fields[1]! do fail "unsafe or inaccessible log file"
    unless json do
      if (← Prim.CoreLogs.flock fd (LOCK_EX ())) != 0 then fail "unsafe or inaccessible log file"
    if json then
      if fields[2]! == 0 then writeAll fd "{".toUTF8
      else
        let _ ← checked (← Prim.CoreLogs.seek fd (-3) (SEEK_END ()))
        writeAll fd ",".toUTF8
    writeAll fd text.toUTF8
    if json then writeAll fd "\n}\n".toUTF8
  finally
    let _ ← Prim.CoreLogs.close fd
    pure ()

def appendLog (path text : String) : IO Unit := append path text false

def appendJson (path member : String) : IO Unit := append path member true

end LeanSudo.Sys.CoreLogs
