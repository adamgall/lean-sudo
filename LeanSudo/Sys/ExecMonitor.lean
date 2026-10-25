import LeanSudo.Sys.ExecChild

namespace LeanSudo.Sys.Exec

open Lean
open Prim.Exec

structure MonitorPlan where
  child : ChildPlan
  slave : Nat
  commands : Nat
  events : Nat
  deriving ToJson, FromJson

def encodeWord (n : UInt32) : ByteArray := ByteArray.mk #[
  n.toUInt8, (n >>> 8).toUInt8, (n >>> 16).toUInt8, (n >>> 24).toUInt8]

def sendEvent (fd : UInt32) (kind value : UInt32) : IO Unit :=
  Prim.Exec.writeAll fd (encodeWord kind ++ encodeWord value)

def signalGroup (pid signal : UInt32) : IO Unit := do
  if (← Prim.Exec.kill (0 - pid) signal) != 0 then discard <| Prim.Exec.kill pid signal

structure MonitorState where
  child : UInt32
  slave : UInt32
  commands : UInt32
  events : UInt32
  signals : UInt32
  savedForeground : UInt32 := 0
  pending : ByteArray := ByteArray.empty
  connected : Bool := true

private partial def monitorLoop (state : MonitorState) : IO UInt32 := do
  let mut state := state
  let (waited, status) ← Prim.Exec.waitpid state.child
    ((K.WNOHANG ()) ||| (K.WUNTRACED ()) ||| (K.WCONTINUED ()))
  if waited == -(Int64.ofInt (K.EINTR ()).toNat) then return ← monitorLoop state
  if waited < 0 then return 1
  if waited > 0 then
    if status &&& (K.waitByteMask ()) == (K.waitSignalMask ()) then
      let foreground ← Prim.Exec.tcgetpgrp state.slave
      if foreground > 0 && foreground.toInt.toNat.toUInt32 != (← Prim.Exec.getpid) then
        state := { state with
          savedForeground := foreground.toInt.toNat.toUInt32 }
      if state.connected then sendEvent state.events 2 status
      else signalGroup state.child (K.SIGCONT ())
    else if status != (K.waitContinued ()) then
      if state.connected then sendEvent state.events 3 status
      return 0
  let commands := if state.connected then state.commands else 0xFFFFFFFF
  let (error, _) ← Prim.Exec.poll #[(state.signals, (K.POLLIN ())), (commands, (K.POLLIN ()))] 20
  if error != 0 && error != (K.EINTR ()) then return 1
  let _ ← Prim.Exec.readSignal state.signals
  if state.connected then
    let (error, bytes) ← Prim.Exec.read state.commands 4096
    if error == 0 && bytes.isEmpty then
      state := { state with connected := false }
      signalGroup state.child (K.SIGHUP ())
      signalGroup state.child (K.SIGCONT ())
    else if error != 0 && error != (K.EINTR ()) && error != (K.EAGAIN ()) then return 1
    else
      let pending := state.pending ++ bytes
      let messages := pending.size / 8
      for i in [:messages] do
        let kind := Prim.Exec.word32 pending (i * 8)
        let value := Prim.Exec.word32 pending (i * 8 + 4)
        if kind == 1 then signalGroup state.child value
        else if kind == 2 then
          let pg := if state.savedForeground != 0 then state.savedForeground else state.child
          discard <| Prim.Exec.tcsetpgrp state.slave pg
          signalGroup state.child (K.SIGCONT ())
        else if kind == 3 then
          discard <| Prim.Exec.tcsetpgrp state.slave (← Prim.Exec.getpid)
          signalGroup state.child (K.SIGCONT ())
      state := { state with pending := pending.extract (messages * 8) pending.size }
  monitorLoop state

def monitorHelper (json : Json) : IO UInt32 := do
  let .ok plan := (fromJson? json : Except String MonitorPlan) | return 127
  let spawned ← IO.mkRef (none : Option UInt32)
  try
    discard <| checkResult "unable to create session" (← Prim.Exec.setsid)
    checkErr "unable to set controlling tty" (← Prim.Exec.ctty plan.slave.toUInt32)
    let childPlan := { plan.child with session := false, commandGroup := true }
    let fds := childPlan.keepFds ++ childPlan.redirects.map (·.1) ++
      #[childPlan.errorFd, plan.slave] ++ childPlan.gate.toArray ++ childPlan.spec.execFd.toArray
    let child ← Helper.spawn "exec-command" (toJson childPlan) (fds.map Nat.toUInt32)
    spawned.set (some child)
    closeQuiet childPlan.errorFd.toUInt32
    for (source, _) in childPlan.redirects do
      if source != plan.slave then closeQuiet source.toUInt32
    if let some gate := childPlan.gate then closeQuiet gate.toUInt32
    discard <| Prim.Exec.setpgid child child
    if childPlan.foreground then discard <| Prim.Exec.tcsetpgrp plan.slave.toUInt32 child
    sendEvent plan.events.toUInt32 1 child
    let signals ← Prim.Exec.signalFd
    monitorLoop {
      child, slave := plan.slave.toUInt32, commands := plan.commands.toUInt32,
      events := plan.events.toUInt32, signals }
  catch error =>
    if let some child ← spawned.get then
      discard <| Prim.Exec.kill (0 - child) (K.SIGKILL ())
      discard <| Prim.Exec.kill child (K.SIGKILL ())
      discard <| Prim.Exec.waitpid child 0
    let failure : ChildError := { message := error.toString }
    try Prim.Exec.writeAll plan.child.errorFd.toUInt32 (toJson failure).compress.toUTF8
    catch _ => pure ()
    return 127

end LeanSudo.Sys.Exec
