import LeanSudo.Sys.ExecUtmp
import LeanSudo.Sys.Prim.CoreFacts
import LeanSudo.Background

namespace LeanSudo.Sys

open Lean
open Prim.Exec

namespace Exec

structure ProcessState where
  uid : UInt32 := 0
  gid : UInt32 := 0
  limits : Array (Option (UInt64 × UInt64)) := #[]
  core : Option (UInt64 × UInt64) := none
  dumpable : Int := -1
  ignored : Array Nat := #[]
  initialized : Bool := false
  deriving Inhabited

private initialize processState : IO.Ref ProcessState ← IO.mkRef {}
private initialize dumpedCore : IO.Ref Bool ← IO.mkRef false

def flushStd : IO Unit := do
  try (← IO.getStdout).flush catch _ => pure ()
  try (← IO.getStderr).flush catch _ => pure ()

def exitRaw (isSignal : Bool) (n : UInt32) : IO Unit := do
  let stopping := #[(K.SIGSTOP ()), (K.SIGTSTP ()), (K.SIGTTIN ()), (K.SIGTTOU ())]
  if isSignal && 1 ≤ n && n.toNat < (K.NSIG ()) && !stopping.contains n then
    discard <| Prim.Exec.setrlimit (K.RLIMIT_CORE ()) 0 0
    discard <| Prim.Exec.signalAction n (Prim.Exec.defaultHandler ())
    discard <| Prim.Exec.raise n
    Prim.Exec.signalMask (0xFFFFFFFFFFFFFFFF ^^^ ((1 : UInt64) <<< (n.toNat - 1).toUInt64))
  let code := if isSignal then min 255 (n.toNat + 128) else min 255 n.toNat
  Prim.Exec.exit code.toUInt32

private def prepare (spec : ExecSpec) (errorFd : UInt32) (filter : ByteArray)
    (keepFds : Array UInt32) : IO ChildPlan := do
  let state ← processState.get
  let mut spec := spec
  if let some profile := spec.apparmorProfile then
    if (← readFirst "/sys/module/apparmor/parameters/enabled") != some 89 then
      spec := { spec with apparmorProfile := none }
    else spec := { spec with apparmorProfile := some profile }
  if let some file := spec.noexecFile then
    if spec.chroot.isNone then
      try
        let facts ← Prim.Exec.stat file
        if facts[2]! &&& (K.S_IFMT ()) != (K.S_IFREG ()) then
          errnoFailure "unable to configure command execution" (K.EACCES ())
        let fd ← checkResult "unable to configure command execution"
          (← Prim.Exec.openFile file (K.O_CLOEXEC ()) 0)
        closeQuiet fd
      catch error =>
        throw (IO.userError s!"unable to configure command execution: {error}")
    spec := { spec with env := mergePreload spec.env file }
  let mut limits := #[]
  for (name, value) in spec.rlimits do
    let some (_, resource) := limitNames.find? (·.1 == name)
      | errnoFailure "unable to configure command execution" (K.EINVAL ())
    limits := limits.filter fun entry => entry.1 != resource.toNat
    if value == "default" then continue
    let user ← match (state.limits[resource.toNat]?).getD none with
      | some limit => pure limit
      | none => Prim.Exec.getrlimit resource
    let requested ← if value == "user" then pure (user.1.toNat, user.2.toNat)
      else match parseLimit value with
        | some limit => pure limit
        | none => errnoFailure "unable to configure command execution" (K.EINVAL ())
    limits := limits.push (resource.toNat, requested.1, requested.2, user.2.toNat)
  return {
    spec
    ruid := if spec.staySetuid then state.uid.toNat else spec.uid
    gid := if spec.staySetuid then state.gid.toNat else spec.gid
    errorFd := errorFd.toNat
    keepFds := keepFds.map UInt32.toNat
    limits
    coreLimit := state.core.map fun (a, b) => (a.toNat, b.toNat)
    dumpable := state.dumpable
    ignored := state.ignored
    seccompFilter := filter.data.map UInt8.toNat }

private def readFailure (hooks : RelayHooks) (bytes : ByteArray) : IO Unit := do
  if bytes.isEmpty then return
  let some text := String.fromUTF8? bytes
    | throw (IO.userError "invalid command error record")
  let .ok json := Json.parse text | throw (IO.userError "invalid command error record")
  let .ok failure := (fromJson? json : Except String ChildError)
    | throw (IO.userError "invalid command error record")
  hooks.onExecError failure.error.toUInt32
  throw (IO.userError failure.message)

private def closePty (pty : Option Pty) : IO Unit := do
  if let some pty := pty then
    discard <| restoreTty pty
    closeQuiet pty.tty
    closeQuiet pty.master
    if pty.slave != 0xFFFFFFFF then closeQuiet pty.slave

private partial def waitOwner (pid : UInt32) : IO Unit := do
  let (result, _) ← Prim.Exec.waitpid pid 0
  if result == -(Int64.ofInt (K.EINTR ()).toNat) then waitOwner pid

private structure Resources where
  owned : Array UInt32
  pty : Option Pty := none
  channels : Array Channel := #[]
  owner : UInt32 := 0
  stateRef : Option (IO.Ref RelayState) := none
  utmp : Option ByteArray := none
  finalStatus : UInt32 := 256

private def run (spec : ExecSpec) (hooks : RelayHooks) (filter : ByteArray)
    (trace : Bool) (keepFds : Array UInt32) : IO ExitStatus := do
  let _ ← match check spec with
    | .ok value => pure value
    | .error error => throw (IO.userError error)
  if spec.background then Background.detach
  dumpedCore.set false
  flushStd
  let (errorReader, errorWriter) ← Prim.Exec.pipe
  let resources ← IO.mkRef ({ owned := #[errorReader, errorWriter] } : Resources)
  try
    let mut pty : Option Pty := none
    let mut owner : UInt32 := 0
    let mut plan ← prepare spec errorWriter filter keepFds
    let anyTty := (← Prim.Exec.isatty 0) || (← Prim.Exec.isatty 1) || (← Prim.Exec.isatty 2)
    if ((spec.usePty && !spec.background) || (← hooks.forcePty)) && anyTty then
      try pty := some (← preparePty) catch error =>
        stderr s!"sudo: {error}\n"
    resources.modify fun state => { state with pty }
    if let some terminal := pty then
      let entry ← beginUtmp terminal spec.utmpUser
      resources.modify fun state => { state with utmp := entry }
    let mut channels ← prepareChannels hooks ((pty.map (·.mask)).getD 0)
    resources.modify fun state => { state with channels }
    let mut redirects := channels.map fun channel => (channel.child.toNat, channel.stream.toNat)
    if let some terminal := pty then
      for fd in [:3] do
        if terminal.mask &&& (1 <<< fd) != 0 then
          redirects := redirects.push (terminal.slave.toNat, fd)
      plan := { plan with
        slave := some terminal.slave.toNat
        foreground := terminal.foreground && !spec.execBackground }
    plan := { plan with
      redirects
      closeFds := redirects.map (·.1) |>.filter (fun fd => fd > 2) }
    let mut gate : Option UInt32 := none
    if trace then
      let (reader, writer) ← Prim.Exec.pipe
      resources.modify fun state => { state with owned := state.owned.push reader |>.push writer }
      plan := { plan with gate := some reader.toNat }
      gate := some writer
    let signals ← Prim.Exec.signalFd
    resources.modify fun state => { state with owned := state.owned.push signals }
    discard <| checkResult "command error pipe"
      (← Prim.Exec.fcntl errorReader (K.F_SETFL ()) (K.O_NONBLOCK ()))
    let mut commands : Option UInt32 := none
    let mut events : Option UInt32 := none
    let fds := keepFds ++ redirects.map (fun pair => pair.1.toUInt32) ++ #[errorWriter] ++
      (plan.gate.toArray.map Nat.toUInt32) ++ (spec.execFd.toArray.map Nat.toUInt32)
    if let some terminal := pty then
      let (commandReader, commandWriter) ← Prim.Exec.pipe ((K.O_CLOEXEC ()) ||| (K.O_NONBLOCK ()))
      resources.modify fun state => {
        state with owned := state.owned.push commandReader |>.push commandWriter }
      let (eventReader, eventWriter) ← Prim.Exec.pipe ((K.O_CLOEXEC ()) ||| (K.O_NONBLOCK ()))
      resources.modify fun state => {
        state with owned := state.owned.push eventReader |>.push eventWriter }
      let monitor : MonitorPlan := {
        child := plan, slave := terminal.slave.toNat,
        commands := commandReader.toNat, events := eventWriter.toNat }
      owner ← Helper.spawn "exec-monitor" (toJson monitor)
        (fds ++ #[terminal.slave, commandReader, eventWriter])
      resources.modify fun state => { state with owner }
      closeQuiet commandReader
      closeQuiet eventWriter
      resources.modify fun state => {
        state with owned := state.owned.filter fun fd => fd != commandReader && fd != eventWriter }
      commands := some commandWriter
      events := some eventReader
    else
      owner ← Helper.spawn "exec-command" (toJson plan) fds
      resources.modify fun state => { state with owner }
      hooks.onSpawn owner
      if let some writer := gate then
        Prim.Exec.writeAll writer (ByteArray.mk #[1])
        closeQuiet writer
        resources.modify fun state => { state with owned := state.owned.filter (· != writer) }
        gate := none
    closeQuiet errorWriter
    resources.modify fun state => { state with owned := state.owned.filter (· != errorWriter) }
    if let some reader := plan.gate then
      closeQuiet reader.toUInt32
      resources.modify fun state => {
        state with owned := state.owned.filter (· != reader.toUInt32) }
    for i in [:channels.size] do
      closeQuiet channels[i]!.child
      channels := channels.set! i { channels[i]! with child := 0xFFFFFFFF }
      resources.modify fun state => { state with channels }
    if let some terminal := pty then
      closeQuiet terminal.slave
      pty := some (← rawTty { terminal with slave := 0xFFFFFFFF })
      resources.modify fun state => { state with pty }
    let started ← IO.monoMsNow
    let initial : RelayState := {
      owner, command := if pty.isSome then 0 else owner, signals, errorFd := errorReader,
      gate, events, commands, pty, channels, tracing := trace,
      deadline := if spec.timeout == 0 then 0 else started + spec.timeout * 1000 }
    let tracked ← IO.mkRef initial
    resources.modify fun state => { state with stateRef := some tracked }
    if spec.background then Background.started
    let (status, failure) ← relay hooks initial tracked
    resources.modify fun state => { state with finalStatus := status }
    if pty.isSome then waitOwner owner
    resources.modify fun state => { state with owner := 0 }
    readFailure hooks failure
    let signal := status &&& (K.waitSignalMask ())
    dumpedCore.set (signal != 0 && status &&& (K.waitCore ()) != 0)
    return if signal != 0 then .signaled signal.toNat
      else .exited ((status >>> (K.waitShift ())) &&& (K.waitByteMask ())).toNat
  catch error =>
    let cleanup ← resources.get
    if cleanup.owner != 0 then
      if let some tracked := cleanup.stateRef then
        let state ← tracked.get
        if state.command != 0 && state.pty.isSome && state.status.isNone then
          signalGroup state.command (K.SIGKILL ())
      let (reaped, _) ← Prim.Exec.waitpid cleanup.owner (K.WNOHANG ())
      if reaped == 0 then
        discard <| Prim.Exec.kill cleanup.owner (K.SIGKILL ())
        waitOwner cleanup.owner
    throw error
  finally
    let cleanup ← resources.get
    if let some entry := cleanup.utmp then finishUtmp entry cleanup.finalStatus
    if let some tracked := cleanup.stateRef then
      let state ← tracked.get
      closeChannels state.channels
      closePty state.pty
    else
      closeChannels cleanup.channels
      closePty cleanup.pty
    for fd in cleanup.owned do closeQuiet fd

end Exec

def initializeProcess (disableCoredump : Bool := true) : IO Unit := do
  for fd in [:3] do
    let result ← Prim.Exec.fcntl fd.toUInt32 (K.F_GETFD ()) 0
    if result != -(Int64.ofInt (K.EBADF ()).toNat) then continue
    let replacement ← Exec.checkResult "unable to open /dev/null"
      (← Prim.Exec.openFile "/dev/null" (K.O_RDWR ()) 0)
    if replacement != fd.toUInt32 then
      Prim.Exec.dup2 replacement fd.toUInt32
      Exec.closeQuiet replacement
  Prim.CoreFacts.initializeLocale
  let mut state ← Exec.processState.get
  if !state.initialized then
    state := { state with uid := (← Prim.Exec.getuid), gid := (← Prim.Exec.getgid) }
    for resource in [:(K.RLIM_NLIMITS ())] do
      let limit ← try pure (some (← Prim.Exec.getrlimit resource.toUInt32)) catch _ => pure none
      state := { state with limits := state.limits.push limit }
    for signal in [1:(K.NSIG ())] do
      if Prim.Exec.supportedSignal signal then
        let action ← Prim.Exec.signalAction signal.toUInt32 (Prim.Exec.defaultHandler ()) 0 0 true
        if action[0]! == 0 && action[1]! == (Prim.Exec.ignoreHandler ()).toUInt64 then
          state := { state with ignored := state.ignored.push signal }
    state := { state with initialized := true }
  if disableCoredump && state.core.isNone then
    let limit ← Prim.Exec.getrlimit (K.RLIMIT_CORE ())
    Exec.checkErr "unable to disable core dumps"
      (← Prim.Exec.setrlimit (K.RLIMIT_CORE ()) 0 limit.2)
    let dumpable ← Prim.Exec.prctl (K.PR_GET_DUMPABLE ())
    discard <| Exec.checkResult "unable to disable core dumps"
      (← Prim.Exec.prctl (K.PR_SET_DUMPABLE ()) 0)
    state := { state with core := some limit, dumpable := dumpable.toInt }
  Exec.processState.set state

def restoreCoreLimit : IO Unit := do
  let state ← Exec.processState.get
  if let some (low, high) := state.core then
    let error ← Prim.Exec.setrlimit (K.RLIMIT_CORE ()) low high
    if error != 0 then Exec.warnLimit (K.RLIMIT_CORE ()) error
    Exec.processState.set { state with core := none }

def lastDumpedCore : IO Bool := Exec.dumpedCore.get

def runCommandPrepared (spec : ExecSpec) (hooks : RelayHooks) (seccompFilter : ByteArray)
    (trace : Bool) (extraEnv : Array String) (keepFds : Array UInt32 := #[]) : IO ExitStatus := do
  let mut env := spec.env
  for entry in extraEnv do
    let name := (entry.splitOn "=").head!
    env := env.filter fun value => !(value.startsWith (name ++ "="))
    env := env.push entry
  Exec.run { spec with env } hooks seccompFilter trace keepFds

def runCommandWithHooks (spec : ExecSpec) (hooks : RelayHooks) : IO ExitStatus :=
  runCommandPrepared spec hooks ByteArray.empty false #[]

def runCommand (spec : ExecSpec) : IO ExitStatus := runCommandWithHooks spec {}

def registerExecHelpers : IO Unit := do
  Helper.register "exec-command" Exec.childHelper
  Helper.register "exec-monitor" Exec.monitorHelper

def exitWith (status : ExitStatus) : IO α := do
  Exec.flushStd
  match status with
  | .exited code => Exec.exitRaw false (min code 255).toUInt32
  | .signaled signal => Exec.exitRaw true (min signal 0xFFFF).toUInt32
  throw (IO.userError "exit failed")

end LeanSudo.Sys
