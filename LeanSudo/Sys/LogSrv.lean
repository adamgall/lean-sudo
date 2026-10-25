import LeanSudo.LogSrv
import LeanSudo.EventLog
import LeanSudo.IoLog
import LeanSudo.Sys.Core
import LeanSudo.Sys.Extra

namespace LeanSudo.Sys.LogSrv
open LeanSudo.LogSrv

@[extern "leansudo_logsrv_connect"]
private opaque connect (host service : @& String) (tls : Bool) (timeout : UInt32)
    (keepalive verify : Bool) (ca cert key : @& String) : IO Unit
@[extern "leansudo_logsrv_send"]
private opaque send (bytes : @& ByteArray) : IO Unit
@[extern "leansudo_logsrv_receive"]
private opaque receive (wait : Bool) : IO (Option ByteArray)
@[extern "leansudo_logsrv_close"]
private opaque closeTransport : IO Unit
@[extern "leansudo_logsrv_relay"]
private opaque relay (mask : UInt32) : IO Unit
@[extern "leansudo_iolog_remote"]
private opaque configureFilter (flags : UInt32) (patterns : @& Array String) : IO Unit
@[extern "leansudo_logsrv_queue_init"]
private opaque queueInit : IO Unit
@[extern "leansudo_logsrv_queue_send"]
private opaque enqueue (bytes : @& ByteArray) : IO Unit
@[extern "leansudo_logsrv_queue_close"]
private opaque queueClose : IO Unit
@[extern "leansudo_logsrv_is_broker"]
private opaque isBroker : IO Bool
@[extern "leansudo_logsrv_clock"]
private opaque awakeTime : IO Nat

/-- sudo's server syntax; brackets disambiguate IPv6 from a port suffix. -/
def endpoint (value : String) : Option (String × String × Bool) := do
  let tls := value.endsWith "(tls)"
  let value := if tls then value.dropEnd 5 |>.toString else value
  let defaultPort := if tls then "30344" else "30343"
  let (host, port) ← if value.startsWith "[" then do
      let parts := value.splitOn "]"
      match parts with
      | [host, rest] =>
        let host := host.drop 1 |>.toString
        if rest.isEmpty then some (host, defaultPort)
        else if rest.startsWith ":" then some (host, rest.drop 1 |>.toString) else none
      | _ => none
    else match value.splitOn ":" with
      | [host] => some (host, defaultPort)
      | [host, port] => some (host, port)
      | _ => none
  let number ← port.toNat?
  if host.isEmpty || number == 0 || number > 65535 then none else some (host, port, tls)

private structure Session where
  settings : Settings
  io : Bool
  ignoreErrors : Bool
  subcommands : Bool := false
  logId : String := ""
  started : Nat
  last : Nat
  elapsed : Nat := 0
  committed : Nat := 0
  commitSeen : Bool := false

initialize current : IO.Ref (Option Session) ← IO.mkRef none

private def timespec (nanos : Nat) : TimeSpec :=
  { seconds := Int.ofNat (nanos / 1000000000), nanoseconds := Int.ofNat (nanos % 1000000000) }

private def sendMessage (message : ClientMessage) : IO Unit := send (encodeClient message)

private def readMessage (wait : Bool) : IO (Option ServerMessage) := do
  let some bytes ← receive wait | return none
  let some message := decodeServer bytes |
    throw (IO.userError s!"unable to unpack ServerMessage size {bytes.size}")
  return some message

private def connectServer (st : Settings) (server : String) : IO Unit := do
  let some (host, port, tls) := endpoint server |
    throw (IO.userError ("invalid log server: " ++ server))
  connect host port tls st.logServerTimeout.toUInt32 st.logServerKeepalive st.logServerVerify
    (st.logServerCabundle.getD "") (st.logServerPeerCert.getD "") (st.logServerPeerKey.getD "")

private def handshake : IO Bool := do
  sendMessage (.hello "sudoers 1.9.17p2")
  match ← readMessage true with
  | some (.hello hello) =>
    if hello.serverId.isEmpty then throw (IO.userError "invalid ServerHello")
    return hello.subcommands
  | some (.error error) => throw (IO.userError ("error message received from server: " ++ error))
  | some (.abort error) => throw (IO.userError ("abort message received from server: " ++ error))
  | _ => throw (IO.userError "invalid ServerHello")

private def connectFirst (st : Settings) (servers : List String) : IO Bool := do
  let mut cause : Option String := none
  for server in servers do
    let connected ← try
      connectServer st server
      pure true
    catch error =>
      let message := error.toString
      if message.startsWith "TLS connection to " then
        let lines := message.splitOn "\n"
        Sys.writeStderr ("sudo: " ++ lines.headD message ++ "\n")
        cause := (lines.drop 1).head?
      closeTransport
      pure false
    -- sudoers fails over connection establishment, not a peer's malformed
    -- handshake: protocol errors from an established connection are final.
    if connected then return ← handshake
  for message in cause do Sys.writeStderr ("sudo: " ++ message ++ "\n")
  throw (IO.userError "unable to connect to log server")

private def consume (s : Session) (message : ServerMessage) : IO Session := do
  match message with
  | .commit time =>
    if !s.io || time.seconds < 0 || time.nanoseconds < 0 || time.nanoseconds >= 1000000000 then
      throw (IO.userError "invalid log server commit point")
    let committed := time.seconds.toNat * 1000000000 + time.nanoseconds.toNat
    if committed < s.committed || committed > s.elapsed then
      throw (IO.userError "invalid log server commit point")
    return { s with committed, commitSeen := true }
  | .logId id =>
    if id.isEmpty then throw (IO.userError "invalid log server log ID")
    return { s with logId := id }
  | .error message => throw (IO.userError ("error message received from server: " ++ message))
  | .abort message => throw (IO.userError ("abort message received from server: " ++ message))
  | .hello _ => throw (IO.userError "unexpected ServerHello")


private partial def awaitId (s : Session) : IO Session := do
  if !s.logId.isEmpty then return s
  let some message ← readMessage true | throw (IO.userError "log server closed connection")
  awaitId (← consume s message)

private partial def awaitCommit (s : Session) : IO Session := do
  if s.commitSeen && s.committed == s.elapsed then return s
  let some message ← readMessage true | throw (IO.userError "log server closed connection")
  awaitCommit (← consume s message)

private partial def drain (s : Session) : IO Session := do
  -- sudoers stops logging on an established-session transport failure; only
  -- initial connection setup fails over. RestartMessage belongs to sendlog.
  let some message ← readMessage false | return s
  drain (← consume s message)

private def failure (s : Session) (error : IO.Error) : IO Unit := do
  closeTransport
  current.set none
  Sys.writeStderr ("sudo: " ++ error.toString ++ "\n")
  if !s.ignoreErrors then
    throw (IO.userError "unexpected child termination condition: 0")

private def info (d : EventLog.Details) : List InfoMessage :=
  d.fields.filterMap fun (key, value) => match value with
    | .string s => some { key, value := .string s }
    | .number n => some { key, value := .number n }
    | .array xs => some { key, value := .strings (xs.filterMap fun x => match x with
        | .string s => some s | _ => none) }
    | _ => none

/-- Close transport and detach relay callbacks, including exceptional command exits. -/
def close : IO Unit := do
  current.set none
  closeTransport
  queueClose


private def streamMask (plan : Option LeanSudo.IoLog.Plan) : UInt32 :=
  match plan with
  | none => 0
  | some p =>
    let bits := [p.stdin, p.stdout, p.stderr, p.ttyin, p.ttyout]
    (bits.zipIdx.foldl (fun (n : Nat) (b, i) => if b then n + 2 ^ i else n) 0).toUInt32
/-- Remote I/O replaces local files, as in sudoers_io. Accept events without I/O
use ignore_logfile_errors; I/O setup and streaming use ignore_iolog_errors. -/
def accept (st : Settings) (details : EventLog.Details) (plan : Option LeanSudo.IoLog.Plan) : IO Unit := do
  if st.logServers.isEmpty || (!st.logAllowed && plan.isNone) then return
  let io := plan.isSome
  let ignoreErrors := if io then st.ignoreIologErrors else st.ignoreLogfileErrors
  try
    let started ← awakeTime
    let subcommands ← connectFirst st st.logServers
    let now ← Sys.eventTime false st.sudoersLocale
    sendMessage (.accept { seconds := now.seconds, nanoseconds := now.nanoseconds } (info details) io)
    let s : Session := {
      settings := st, io, ignoreErrors, subcommands
      started, last := started }
    let s ← if io then awaitId s else pure s
    if let some p := plan then
      configureFilter ((if p.ignoreErrors then 128 else 0) + (if p.logPasswords then 256 else 0)) p.passpromptRegex
      relay (streamMask plan)
    queueInit
    current.set (some s)
  catch error =>
    close
    Sys.writeStderr ("sudo: " ++ error.toString ++ "\n")
    if !ignoreErrors then
      throw (IO.userError (if io then "error initializing I/O plugin sudoers_io"
        else "sudoers_audit: unable to log accept event"))

/-- Reject and alert records are independent short-lived connections. -/
def event (st : Settings) (details : EventLog.Details) (reason : String) (alert : Bool := false) : IO Unit := do
  if st.logServers.isEmpty || (!alert && !st.logDenied) then return
  if ← isBroker then
    let some s ← current.get | return
    if !s.subcommands then return
    let now ← Sys.eventTime false st.sudoersLocale
    let time : TimeSpec := { seconds := now.seconds, nanoseconds := now.nanoseconds }
    -- sudo's subcommand path retains the initially accepted closure's empty reason.
    enqueue (encodeClient (if alert then .alert time "" (info details) else .reject time "" (info details)))
    return
  try
    let _ ← connectFirst st st.logServers
    let now ← Sys.eventTime false st.sudoersLocale
    let time : TimeSpec := { seconds := now.seconds, nanoseconds := now.nanoseconds }
    sendMessage (if alert then .alert time reason (info details) else .reject time reason (info details))
  catch error => Sys.writeStderr ("sudo: " ++ error.toString ++ "\n")
  finally closeTransport

@[export leansudo_logsrv_poll]
def poll : IO Unit := do
  let some s ← current.get | return
  try current.set (some (← drain s))
  catch error => failure s error

/-- Called only in the policy broker. Encoded events travel to the original
process, which alone owns the TLS state and serializes event and I/O messages. -/
def subcommand (details : EventLog.Details) (reason : Option String) : IO Unit := do
  let some s ← current.get | return
  if !s.subcommands then return
  let now ← Sys.eventTime false s.settings.sudoersLocale
  let time : TimeSpec := { seconds := now.seconds, nanoseconds := now.nanoseconds }
  let message := match reason with
    | some _ => ClientMessage.reject time "" (info details)
    | none => .accept time (info details) s.io
  enqueue (encodeClient message)

@[export leansudo_logsrv_subcommand_wire]
def subcommandWire (bytes : ByteArray) : IO Unit := do
  let some s ← current.get | return
  if !s.subcommands then return
  try
    send bytes
    current.set (some (← drain s))
  catch error => failure s error

/-- Invoked synchronously by the privileged relay, never by the command child.
Commit offsets track durable storage; fatal transport errors stop the command. -/
@[export leansudo_logsrv_io_event]
def ioEvent (event : UInt32) (data : ByteArray) (a b : UInt32) : IO Unit := do
  let some s ← current.get | return
  try
    let now ← awakeTime
    let delay := now - s.last
    let time := timespec delay
    let message := if event.toNat < 5 then ClientMessage.io event.toNat time data
      else if event == 5 then .winsize time a.toNat b.toNat
      else .suspend time (String.fromUTF8! data)
    let bytes := encodeClient message
    let s := { s with last := now, elapsed := s.elapsed + delay }
    send bytes
    let s ← drain s
    current.set (some s)
  catch error => failure s error

/-- I/O sessions send ExitMessage and wait for their final durable commit,
independently of local log_exit_status. Sudo's audit-only client just closes. -/
def finish (exitValue : Nat) (signal : String) (dumpedCore : Bool)
    (error : String := "") : IO Unit := do
  let some s ← current.get | return
  if !s.io then
    close
    return
  let s := { s with commitSeen := false }
  try
    let runtime := (← awakeTime) - s.started
    let bytes := encodeClient (.exit (timespec runtime) (Int.ofNat exitValue) dumpedCore signal error)
    send bytes
    let _ ← awaitCommit s
    pure ()
  catch error => failure s error
  finally close

end LeanSudo.Sys.LogSrv
