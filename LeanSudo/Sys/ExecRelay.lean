import LeanSudo.Sys.ExecMonitor
import LeanSudo.Sys.Relay
import LeanSudo.Sys.Core
import LeanSudo.Sys.Prim.IoLog

namespace LeanSudo.Sys.Exec

open Prim.Exec

structure Pty where
  tty : UInt32
  master : UInt32
  slave : UInt32
  mask : Nat
  original : ByteArray
  rows : UInt32
  cols : UInt32
  foreground : Bool
  raw : IO.Ref Bool

structure Channel where
  parent : UInt32
  child : UInt32
  stream : UInt32
  pending : ByteArray := ByteArray.empty
  offset : Nat := 0
  active : Bool := true
  deriving Inhabited

structure RelayState where
  owner : UInt32
  command : UInt32
  signals : UInt32
  errorFd : UInt32
  gate : Option UInt32
  events : Option UInt32 := none
  commands : Option UInt32 := none
  pty : Option Pty := none
  channels : Array Channel := #[]
  errorBytes : ByteArray := ByteArray.empty
  eventBytes : ByteArray := ByteArray.empty
  inputBytes : ByteArray := ByteArray.empty
  inputOffset : Nat := 0
  inputOpen : Bool := true
  masterOpen : Bool := true
  errorOpen : Bool := true
  deadline : Nat := 0
  terminating : Bool := false
  status : Option UInt32 := none
  ownerExited : Bool := false
  tracing : Bool := false

private def dimension (name : String) (fallback : UInt32) : IO UInt32 := do
  let some text ← IO.getEnv name | return fallback
  let chars := text.toList.dropWhile fun c => c == ' ' || ('\t' ≤ c && c ≤ '\r')
  let chars := if chars.head? == some '+' then chars.drop 1 else chars
  let some n := (String.ofList chars).toNat? | return fallback
  return if 0 < n && n ≤ 0x7FFFFFFF then n.toUInt32 else fallback

def preparePty (owner : UInt32) : IO (Option Pty) := do
  let opened ← Prim.Exec.openFile "/dev/tty"
    ((K.O_RDWR ()) ||| (K.O_NOCTTY ()) ||| (K.O_CLOEXEC ())) 0
  if opened < 0 then return none
  let tty := opened.toInt.toNat.toUInt32
  let allocated ← IO.mkRef (none : Option (UInt32 × UInt32))
  try
    let ttyGroup := ((← Sys.getgrnam "tty").map (·.gid.toUInt32)).getD 0xFFFFFFFF
    let original ← Prim.Exec.tcgetattr tty
    let (r, c) ← try Prim.Exec.winsize tty catch _ => pure (0, 0)
    let rows ← if r != 0 && c != 0 then pure r else dimension "LINES" 24
    let cols ← if r != 0 && c != 0 then pure c else dimension "COLUMNS" 80
    let pair ← Prim.Exec.openpty original r c
    allocated.set (some pair)
    try Prim.IoLog.chown pair.2 owner ttyGroup catch error =>
      throw (IO.userError s!"unable to allocate pty: {error}")
    let master := pair.1
    let slave := pair.2
    discard <| checkResult "unable to allocate pty"
      (← Prim.Exec.fcntl master (K.F_SETFD ()) (K.FD_CLOEXEC ()))
    discard <| checkResult "unable to allocate pty"
      (← Prim.Exec.fcntl slave (K.F_SETFD ()) (K.FD_CLOEXEC ()))
    let flags ← checkResult "unable to allocate pty" (← Prim.Exec.fcntl master (K.F_GETFL ()) 0)
    discard <| checkResult "unable to allocate pty"
      (← Prim.Exec.fcntl master (K.F_SETFL ()) (flags ||| (K.O_NONBLOCK ())))
    let mut mask := 0
    let group ← Prim.Exec.getpgid 0
    for fd in [:3] do
      if (← Prim.Exec.isatty fd.toUInt32) && (← Prim.Exec.tcgetpgrp fd.toUInt32) == group then
        mask := mask ||| (1 <<< fd)
    let foreground := (← Prim.Exec.tcgetpgrp tty) == group
    let raw ← IO.mkRef false
    return some { tty, master, slave, mask, original, rows, cols, foreground, raw }
  catch error =>
    if let some (master, slave) ← allocated.get then
      closeQuiet master
      closeQuiet slave
    closeQuiet tty
    throw error

def restoreTty (pty : Pty) : IO Pty := do
  if ← pty.raw.get then
    let mut error ← Prim.Exec.tcsetattr pty.tty (K.TCSADRAIN ()) pty.original
    while error == (K.EINTR ()) do error ← Prim.Exec.tcsetattr pty.tty (K.TCSADRAIN ()) pty.original
    if error == 0 then pty.raw.set false
  return pty

def rawTty (pty : Pty) : IO Pty := do
  if (← pty.raw.get) || !pty.foreground then return pty
  let raw ← Prim.Exec.cfmakeraw pty.original
  let error ← Prim.Exec.tcsetattr pty.tty (K.TCSADRAIN ()) raw
  if error == 0 then pty.raw.set true
  return pty

def refreshForeground (pty : Pty) : IO Pty := do
  return { pty with foreground := (← Prim.Exec.tcgetpgrp pty.tty) == (← Prim.Exec.getpgid 0) }

private def emit (hooks : RelayHooks) (stream : UInt32) (bytes : ByteArray) : IO Unit := do
  unless ← hooks.onStream stream bytes do throw (IO.userError "unable to write I/O log")
  let permitted ← if stream == 0 || stream == 3 then hooks.onInput bytes
    else hooks.onOutput (if stream == 4 then 1 else stream) bytes
  unless permitted do throw (IO.userError "unable to write I/O log")

def closeChannels (channels : Array Channel) : IO Unit := do
  for channel in channels do
    if channel.active then closeQuiet channel.parent
    if channel.child != 0xFFFFFFFF then closeQuiet channel.child

def prepareChannels (hooks : RelayHooks) (mask : Nat) : IO (Array Channel) := do
  let channels ← IO.mkRef (#[] : Array Channel)
  try
    for stream in [:3] do
      if mask &&& (1 <<< stream) != 0 || !(← hooks.needsStream stream.toUInt32) then continue
      let (reader, writer) ← Prim.Exec.pipe
      let parent := if stream == 0 then writer else reader
      let child := if stream == 0 then reader else writer
      channels.modify (·.push { parent, child, stream := stream.toUInt32 })
      discard <| checkResult "unable to create I/O logging pipes"
        (← Prim.Exec.fcntl parent (K.F_SETFL ()) (K.O_NONBLOCK ()))
    return ← channels.get
  catch error =>
    closeChannels (← channels.get)
    throw error

private def pumpChannel (hooks : RelayHooks) (channel : Channel) : IO Channel := do
  if !channel.active then return channel
  if channel.stream == 0 && channel.offset < channel.pending.size then
    let (error, count) ← Prim.Exec.write channel.parent channel.pending channel.offset.toUInt32
      (channel.pending.size - channel.offset).toUInt32
    if error == (K.EINTR ()) || error == (K.EAGAIN ()) then return channel
    if error != 0 then
      closeQuiet channel.parent
      return { channel with active := false }
    let offset := channel.offset + count.toNat
    return if offset == channel.pending.size then
      { channel with pending := ByteArray.empty, offset := 0 }
      else { channel with offset }
  let fd := if channel.stream == 0 then 0 else channel.parent
  let (error, bytes) ← Prim.Exec.read fd 8192
  if error == (K.EINTR ()) || error == (K.EAGAIN ()) then return channel
  if error != 0 || bytes.isEmpty then
    closeQuiet channel.parent
    return { channel with active := false }
  emit hooks channel.stream bytes
  if channel.stream == 0 then return { channel with pending := bytes, offset := 0 }
  Prim.Exec.writeAll channel.stream bytes
  return channel

private def stopSelf (signal : UInt32) (group : Bool) : IO Unit := do
  let old ← if signal == (K.SIGSTOP ()) then pure #[] else
    Prim.Exec.signalAction signal (Prim.Exec.defaultHandler ())
  if group then
    let pg ← Prim.Exec.getpgid 0
    discard <| Prim.Exec.kill (0 - pg.toInt.toNat.toUInt32) signal
  else discard <| Prim.Exec.raise signal
  Prim.Exec.signalMask (0xFFFFFFFFFFFFFFFF ^^^ ((1 : UInt64) <<< (signal.toNat - 1).toUInt64))
  Prim.Exec.signalMask 0xFFFFFFFFFFFFFFFF
  if signal != (K.SIGSTOP ()) && old[0]! == 0 then
    discard <| Prim.Exec.signalAction signal old[1]!.toUSize old[2]!.toUInt32 old[3]!

private def sendControl (state : RelayState) (kind value : UInt32) : IO Unit := do
  if let some fd := state.commands then sendEvent fd kind value

private def stopped (hooks : RelayHooks) (state : RelayState) (signal : UInt32) :
    IO RelayState := do
  if let some pty := state.pty then
    let pty ← refreshForeground pty
    if (signal == (K.SIGTTIN ()) || signal == (K.SIGTTOU ())) && pty.foreground then
      let pty ← rawTty pty
      sendControl state 2 0
      return { state with pty := some pty }
    let pty ← restoreTty pty
    hooks.onSuspend signal
    stopSelf signal true
    hooks.onSuspend (K.SIGCONT ())
    let pty ← refreshForeground pty >>= rawTty
    sendControl state (if pty.foreground then 2 else 3) 0
    return { state with pty := some pty }
  let tty ← Prim.Exec.openFile "/dev/tty" ((K.O_RDWR ()) ||| (K.O_NOCTTY ()) ||| (K.O_CLOEXEC ())) 0
  let saved ← if tty >= 0 then Prim.Exec.tcgetpgrp tty.toInt.toNat.toUInt32 else pure (-1)
  let group ← Prim.Exec.getpgid 0
  if (signal == (K.SIGTTIN ()) || signal == (K.SIGTTOU ())) && saved == group then
    let commandGroup ← Prim.Exec.getpgid state.command
    if commandGroup > 0 && commandGroup != group &&
        (← Prim.Exec.tcsetpgrp tty.toInt.toNat.toUInt32 commandGroup.toInt.toNat.toUInt32) == 0 then
      signalGroup commandGroup.toInt.toNat.toUInt32 (K.SIGCONT ())
      closeQuiet tty.toInt.toNat.toUInt32
      return state
  hooks.onSuspend signal
  stopSelf signal false
  hooks.onSuspend (K.SIGCONT ())
  if tty >= 0 then
    if saved != group && saved >= 0 then
      discard <| Prim.Exec.tcsetpgrp tty.toInt.toNat.toUInt32 saved.toInt.toNat.toUInt32
    closeQuiet tty.toInt.toNat.toUInt32
  return state

private def shouldForward (record : Prim.Exec.SignalInfo) (child : UInt32) (pty : Bool) :
    IO Bool := do
  let forwarded := #[(K.SIGINT ()), (K.SIGQUIT ()), (K.SIGTSTP ()), (K.SIGTERM ()),
    (K.SIGHUP ()), (K.SIGALRM ()),
    (K.SIGUSR1 ()), (K.SIGUSR2 ()), (K.SIGPIPE ()), (K.SIGWINCH ()), (K.SIGCONT ())]
  unless forwarded.contains record.signo do return false
  let fromUser := record.code <= 0 && record.pid > 0
  let pg ← if fromUser then Prim.Exec.getpgid record.pid else pure (-1)
  let sid ← if fromUser then Prim.Exec.getsid record.pid else pure (-1)
  if fromUser then
    if record.pid == child then return false
    if !pty && pg >= 0 && (pg.toInt.toNat == child.toNat ||
        pg.toInt.toNat == (← Prim.Exec.getpid).toNat) then return false
    if pty && sid >= 0 && sid.toInt.toNat == child.toNat then return false
  if record.signo == (K.SIGINT ()) || record.signo == (K.SIGQUIT ()) ||
      record.signo == (K.SIGTSTP ()) ||
      (!pty && record.signo == (K.SIGWINCH ())) then
    if !fromUser then return false
    if pty && pg >= 0 && pg == (← Prim.Exec.getpgid 0) then return false
  return true

private def terminate (state : RelayState) : IO RelayState := do
  if state.command == 0 then return state
  let send := fun signal => if state.pty.isSome then signalGroup state.command signal
    else do discard <| Prim.Exec.kill state.command signal
  send (K.SIGHUP ())
  send (K.SIGTERM ())
  return { state with terminating := true, deadline := (← IO.monoMsNow) + 2000 }

private partial def signals (hooks : RelayHooks) (state : RelayState) : IO RelayState := do
  let some record ← Prim.Exec.readSignal state.signals | return state
  hooks.onSignal record.signo
  let mut state := state
  if record.signo == (K.SIGWINCH ()) then
    if let some pty := state.pty then
      let (rows, cols) ← try Prim.Exec.winsize pty.tty catch _ => pure (pty.rows, pty.cols)
      if rows != pty.rows || cols != pty.cols then
        hooks.onWindow rows cols
        discard <| Prim.Exec.setWinsize pty.master rows cols
        sendControl state 1 (K.SIGWINCH ())
        state := { state with pty := some { pty with rows, cols } }
    else if ← shouldForward record state.command false then
      discard <| Prim.Exec.kill state.command record.signo
  else if record.signo == (K.SIGCONT ()) && state.pty.isSome then
    if let some previous := state.pty then
      let pty ← refreshForeground previous
      let pty ← if pty.foreground && !(← pty.raw.get) then
          sendControl state 2 0
          rawTty pty
        else
          if !pty.foreground && previous.foreground then sendControl state 3 0
          pure pty
      state := { state with pty := some pty }
  else if record.signo != (K.SIGCHLD ()) &&
      (← shouldForward record state.command state.pty.isSome) then
    if record.signo == (K.SIGALRM ()) then state ← terminate state
    else if state.pty.isSome then sendControl state 1 record.signo
    else discard <| Prim.Exec.kill state.command record.signo
  signals hooks state

private def timer (state : RelayState) : IO RelayState := do
  if state.deadline == 0 || (← IO.monoMsNow) < state.deadline then return state
  if !state.terminating then return ← terminate state
  if state.command != 0 then
    if state.pty.isSome then signalGroup state.command (K.SIGKILL ())
    else discard <| Prim.Exec.kill state.command (K.SIGKILL ())
  return { state with deadline := 0 }

private def pumpMaster (hooks : RelayHooks) (state : RelayState) : IO RelayState := do
  let some pty := state.pty | return state
  let (error, bytes) ← Prim.Exec.read pty.master 8192
  if error == (K.EINTR ()) || error == (K.EAGAIN ()) then return state
  if error != 0 || bytes.isEmpty then return { state with masterOpen := false }
  emit hooks 4 bytes
  Prim.Exec.writeAll pty.tty bytes
  return state

private def flushInput (state : RelayState) : IO RelayState := do
  let some pty := state.pty | return state
  if state.inputOffset >= state.inputBytes.size then return state
  let (error, count) ← Prim.Exec.write pty.master state.inputBytes state.inputOffset.toUInt32
    (state.inputBytes.size - state.inputOffset).toUInt32
  if error == (K.EINTR ()) || error == (K.EAGAIN ()) then return state
  let offset := state.inputOffset + count.toNat
  return if error != 0 || offset >= state.inputBytes.size then
    { state with inputBytes := ByteArray.empty, inputOffset := 0 }
    else { state with inputOffset := offset }

private def pumpEvents (hooks : RelayHooks) (state : RelayState) (tracked : IO.Ref RelayState) :
    IO RelayState := do
  let some fd := state.events | return state
  let (error, bytes) ← Prim.Exec.read fd 4096
  if error == (K.EINTR ()) || error == (K.EAGAIN ()) then return state
  if error != 0 then errnoFailure "command monitor" error
  if bytes.isEmpty then return state
  let pending := state.eventBytes ++ bytes
  let mut state := state
  for i in [:pending.size / 8] do
    let kind := Prim.Exec.word32 pending (i * 8)
    let value := Prim.Exec.word32 pending (i * 8 + 4)
    if kind == 1 then
      state := { state with command := value }
      tracked.set state
      hooks.onSpawn value
      if let some gate := state.gate then
        Prim.Exec.writeAll gate (ByteArray.mk #[1])
        state := { state with gate := none }
    else if kind == 2 then
      state ← stopped hooks state ((value >>> (K.waitShift ())) &&& (K.waitByteMask ()))
    else if kind == 3 then state := { state with status := some value }
  return { state with eventBytes := pending.extract (pending.size / 8 * 8) pending.size }

private def pumpError (state : RelayState) : IO RelayState := do
  if !state.errorOpen then return state
  let (error, bytes) ← Prim.Exec.read state.errorFd 8192
  if error == (K.EINTR ()) || error == (K.EAGAIN ()) then return state
  if error != 0 then errnoFailure "command error pipe" error
  if bytes.isEmpty then return { state with errorOpen := false }
  if state.errorBytes.size + bytes.size > 1048576 then
    throw (IO.userError "invalid command error record")
  return { state with errorBytes := state.errorBytes ++ bytes }

private def reap (hooks : RelayHooks) (state : RelayState) : IO RelayState := do
  let (pid, status) ← Prim.Exec.waitpid (if state.tracing then 0xFFFFFFFF else state.owner)
    ((K.WNOHANG ()) ||| (K.WUNTRACED ()) ||| (K.WCONTINUED ()) |||
      if state.tracing then (K.WALL ()) else 0)
  if pid == 0 || pid == -(Int64.ofInt (K.EINTR ()).toNat) ||
      (pid == -(Int64.ofInt (K.ECHILD ()).toNat) && state.ownerExited) then
    return state
  if pid < 0 then errnoFailure "waitpid" (-pid).toInt.toNat.toUInt32
  let pid := pid.toInt.toNat.toUInt32
  if ← hooks.onChild pid status then return state
  if pid != state.owner then return state
  if status &&& (K.waitByteMask ()) == (K.waitSignalMask ()) then
    if state.pty.isNone then
      stopped hooks state ((status >>> (K.waitShift ())) &&& (K.waitByteMask ())) else pure state
  else if status == (K.waitContinued ()) then pure state
  else return { state with
    ownerExited := true
    status := if state.pty.isNone then some status else state.status }

private partial def drain (hooks : RelayHooks) (state : RelayState)
    (tracked : IO.Ref RelayState) : IO RelayState := do
  let mut state := state
  let mut fds := #[]
  if let some pty := state.pty then
    if state.masterOpen then fds := fds.push (pty.master, (K.POLLIN ()))
  for channel in state.channels do
    if channel.active && channel.stream != 0 then fds := fds.push (channel.parent, (K.POLLIN ()))
  if fds.isEmpty then return state
  let (error, ready) ← Prim.Exec.poll fds 100
  if error == (K.EINTR ()) then return ← drain hooks state tracked
  if error != 0 || ready.all (· == 0) then return state
  let mut index := 0
  if state.pty.isSome && state.masterOpen then
    if ready[index]! != 0 then state ← pumpMaster hooks state
    index := index + 1
  for i in [:state.channels.size] do
    let channel := state.channels[i]!
    if channel.active && channel.stream != 0 then
      if ready[index]! != 0 then
        state := { state with channels := state.channels.set! i (← pumpChannel hooks channel) }
        tracked.set state
      index := index + 1
  drain hooks state tracked

partial def relay (hooks : RelayHooks) (state : RelayState) (tracked : IO.Ref RelayState) :
    IO (UInt32 × ByteArray) := do
  tracked.set state
  let mut state ← reap hooks state
  state ← pumpEvents hooks state tracked
  state ← pumpError state
  tracked.set state
  if let some status := state.status then
    state ← drain hooks state tracked
    state ← pumpError state
    tracked.set state
    hooks.onTick
    hooks.onFinish status
    return (status, state.errorBytes)
  if state.ownerExited then throw (IO.userError "command monitor exited unexpectedly")
  hooks.onTick
  state ← timer state
  let mut fds := #[(state.signals, (K.POLLIN ())),
    (if state.errorOpen then state.errorFd else 0xFFFFFFFF, (K.POLLIN ())),
    (state.events.getD 0xFFFFFFFF, (K.POLLIN ()))]
  let mut masterEvents := 0
  if state.masterOpen then masterEvents := masterEvents ||| (K.POLLIN ())
  if state.inputOffset < state.inputBytes.size then masterEvents := masterEvents ||| (K.POLLOUT ())
  fds := fds.push ((state.pty.map (·.master)).getD 0xFFFFFFFF, masterEvents)
  let tty := match state.pty with
    | some pty => if state.inputOpen && pty.foreground && state.inputBytes.isEmpty then pty.tty
      else 0xFFFFFFFF
    | none => 0xFFFFFFFF
  fds := fds.push (tty, (K.POLLIN ()))
  for channel in state.channels do
    let pending := channel.stream == 0 && channel.offset < channel.pending.size
    let fd := if !channel.active then 0xFFFFFFFF else
      if channel.stream == 0 && !pending then 0 else channel.parent
    fds := fds.push (fd, if pending then (K.POLLOUT ()) else (K.POLLIN ()))
  let (error, ready) ← Prim.Exec.poll fds 10
  if error == (K.EINTR ()) then return ← relay hooks state tracked
  checkErr "poll" error
  for i in [:state.channels.size] do
    if ready[i + 5]! != 0 then
      let channel ← pumpChannel hooks state.channels[i]!
      state := { state with channels := state.channels.set! i channel }
      tracked.set state
  if ready[3]! &&& ((K.POLLIN ()) ||| (K.POLLHUP ()) ||| (K.POLLERR ())) != 0 then
    state ← pumpMaster hooks state
  if ready[3]! &&& (K.POLLOUT ()) != 0 then state ← flushInput state
  if ready[4]! != 0 then
    let (error, bytes) ← Prim.Exec.read tty 4096
    if error == 0 && !bytes.isEmpty then
      emit hooks 3 bytes
      state := { state with inputBytes := bytes, inputOffset := 0 }
      state ← flushInput state
    else if error != (K.EINTR ()) && error != (K.EAGAIN ()) then
      if error == (K.EIO ()) then
        if let some pty := state.pty then
          state := { state with pty := some (← refreshForeground pty) }
      else state := { state with inputOpen := false }
  state ← signals hooks state
  relay hooks state tracked

end LeanSudo.Sys.Exec
