import LeanSudo.Sys.Prim.Exec

namespace LeanSudo.Sys.FrontSignals

open Prim.Exec

private initialize pending : IO.Ref UInt64 ← IO.mkRef 0

private def bit (signal : UInt32) : UInt64 := (1 : UInt64) <<< (signal.toUInt64 - 1)

def signals : Array UInt32 :=
  #[K.SIGHUP (), K.SIGINT (), K.SIGQUIT (), K.SIGTERM (), K.SIGTSTP (), K.SIGALRM (),
    K.SIGUSR1 (), K.SIGUSR2 ()]

def mask : UInt64 := signals.foldl (fun acc signal => acc ||| bit signal) 0

def mark (signal : UInt32) : IO Unit := do
  if signals.contains signal then pending.modify (· ||| bit signal)

private partial def drain (fd : UInt32) : IO Unit := do
  let some info ← readSignal fd | return
  mark info.signo
  drain fd

def collect : IO Unit := do
  let fd ← signalFd mask
  try drain fd finally close fd

private def suspend : IO Unit := do
  let stop := K.SIGTSTP ()
  discard <| signalAction stop (defaultHandler ())
  discard <| raise stop
  signalMask (0xFFFFFFFFFFFFFFFF ^^^ bit stop)
  signalMask 0xFFFFFFFFFFFFFFFF

def terminated : IO (Option UInt32) := do
  collect
  let set ← pending.get
  let terminal := (List.range (K.NSIG ())).find? fun number =>
    let signal := number.toUInt32
    signal != K.SIGTSTP () && signals.contains signal && set &&& bit signal != 0
  if let some number := terminal then return some number.toUInt32
  if set &&& bit (K.SIGTSTP ()) != 0 then suspend
  return none

end LeanSudo.Sys.FrontSignals
