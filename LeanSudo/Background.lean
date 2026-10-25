import LeanSudo.Cli
import LeanSudo.Sys.Core
import LeanSudo.Helper

namespace LeanSudo.Background

open Lean
open Sys.Prim.Exec

private structure Plan where
  argv0 : String
  args : List String
  environment : List (String × String)
  directory : Nat
  status : Nat
  pid : Nat
  ppid : Nat
  deriving ToJson, FromJson

private initialize session : IO.Ref (Option Plan) ← IO.mkRef none
private initialize notifier : IO.Ref (Option UInt32) ← IO.mkRef none

def originalArgv0 : IO (Option String) := return (← session.get).map (·.argv0)

def invokingProcess : IO (Option (Nat × Nat)) :=
  return (← session.get).map fun plan => (plan.pid, plan.ppid)

private def checked (error : UInt32) : IO Unit := do
  if error != 0 then throw (IO.userError (← strerror error))

private def descriptor (result : Int64) : IO UInt32 := do
  if result < 0 then checked (-result).toInt.toNat.toUInt32
  return result.toInt.toNat.toUInt32

private def closeQuiet (fd : UInt32) : IO Unit := do
  try close fd catch _ => pure ()

def detach : IO Unit := do
  unless (← session.get).isSome do throw (IO.userError "invalid background session")
  checked (← setpgid 0 0)
  Sys.CoreLogs.setSyslogPidOverride none

def started : IO Unit := do
  if let some fd ← notifier.get then
    writeAll fd (ByteArray.mk #[0])
    notifier.set none
    closeQuiet fd

private def helper (run : List String → IO UInt32) (json : Json) : IO UInt32 := do
  let plan ← IO.ofExcept (fromJson? json : Except String Plan)
  unless plan.directory ≤ (K.INT_MAX ()).toNat && plan.status ≤ (K.INT_MAX ()).toNat &&
      !plan.argv0.contains '\x00' && plan.args.all (fun arg => !arg.contains '\x00') &&
      plan.environment.all (fun (name, value) =>
        !name.isEmpty && !name.contains '=' && !name.contains '\x00' && !value.contains '\x00') do
    throw (IO.userError "invalid background session plan")
  let fd := plan.status.toUInt32
  discard <| descriptor (← fcntl fd (K.F_SETFD ()) (K.FD_CLOEXEC ()))
  checked (← fchdir plan.directory.toUInt32)
  closeQuiet plan.directory.toUInt32
  checked (← clearenv)
  for (name, value) in plan.environment do checked (← setenv name value)
  session.set (some plan)
  notifier.set (some fd)
  Sys.CoreLogs.setSyslogPidOverride (some plan.pid)
  try run plan.args
  finally
    if let some pending ← notifier.get then closeQuiet pending
    notifier.set none

def register (run : List String → IO UInt32) : IO Unit :=
  Helper.register "background-session" (helper run)

private partial def waitSession (child reader signals : UInt32) : IO UInt32 := do
  let (error, bytes) ← read reader 1
  if error == 0 && bytes.size == 1 then return bytes[0]!.toUInt32
  if error != 0 && error != K.EAGAIN () && error != K.EINTR () then checked error
  let (pid, status) ← waitpid child (K.WNOHANG ())
  if pid < 0 && pid != -(Int64.ofInt (K.EINTR ()).toNat) then
    checked (-pid).toInt.toNat.toUInt32
  if pid > 0 then
    let (error, bytes) ← read reader 1
    if error == 0 && bytes.size == 1 then return bytes[0]!.toUInt32
    let signal := status &&& K.waitSignalMask ()
    return if signal == 0 then (status >>> K.waitShift ()) &&& K.waitByteMask ()
      else 128 + signal
  let (error, ready) ← poll #[(reader, K.POLLIN ()), (signals, K.POLLIN ())] 20
  if error != 0 && error != K.EINTR () then checked error
  if ready[1]?.getD 0 != 0 then discard <| readSignal signals
  waitSession child reader signals

private def launch (argv0 : String) (args : List String)
    (environment : List (String × String)) : IO UInt32 := do
  let owned ← IO.mkRef (#[] : Array UInt32)
  let spawned ← IO.mkRef (none : Option UInt32)
  try
    let directory ← descriptor (← openFile "."
      (Sys.Prim.Posix.O_PATH () ||| Sys.Prim.Posix.O_DIRECTORY () ||| K.O_CLOEXEC ()) 0)
    owned.modify (·.push directory)
    let (reader, writer) ← pipe (K.O_CLOEXEC () ||| K.O_NONBLOCK ())
    owned.modify (fun fds => fds.push reader |>.push writer)
    let signals ← signalFd
    owned.modify (·.push signals)
    let plan : Plan := {
      argv0, args, environment
      directory := directory.toNat, status := writer.toNat
      pid := (← getpid).toNat, ppid := (← getppid).toNat }
    let child ← Helper.spawn "background-session" (toJson plan) #[writer, directory]
    spawned.set (some child)
    closeQuiet writer
    owned.modify (·.filter (· != writer))
    waitSession child reader signals
  catch error =>
    if let some child ← spawned.get then
      discard <| kill child (K.SIGKILL ())
      discard <| waitpid child 0
    throw error
  finally
    for fd in (← owned.get) do closeQuiet fd

def launchIfRequested (args : List String) : IO (Option UInt32) := do
  if (← session.get).isSome || (← Sys.geteuid) != 0 then return none
  let raw ← IO.FS.readBinFile "/proc/self/cmdline"
  let some _ := String.fromUTF8? raw | return none
  let first := ByteArray.mk ((raw.data.toList.takeWhile (· != 0)).toArray)
  let some argv0 := String.fromUTF8? first | return none
  let environment ← Sys.environ
  let .ok opts := (Cli.parseArgs argv0 args environment).result | return none
  if opts.mode != .run || !opts.background then return none
  return some (← launch argv0 args environment)

end LeanSudo.Background
