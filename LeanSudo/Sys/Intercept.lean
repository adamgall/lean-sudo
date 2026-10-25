import LeanSudo.Sys.InterceptDso
import LeanSudo.Sys.Relay
import LeanSudo.Sys.LogSrv

namespace LeanSudo.Sys.Intercept

abbrev Request := InterceptTrace.Request

private inductive Monitor where
  | trace (state : IO.Ref InterceptTrace.State) (check : Request → IO Bool)
  | dso (state : IO.Ref InterceptDso.State) (check : Request → IO Bool)

private initialize monitor : IO.Ref (Option Monitor) ← IO.mkRef none

private def start (trace verify logOnly : Bool) (check : Request → IO Bool) : IO Unit := do
  if (← monitor.get).isSome then
    throw (IO.userError "interception already active")
  let check := fun request => LogSrv.withBroker (check request)
  try
    if trace && (← Prim.Intercept.traceSupported) then
      let arch := if (← Prim.Intercept.architecture) = 1 then
        LeanSudo.Intercept.Seccomp.Architecture.x86_64 else .aarch64
      let pageSize := (← Prim.Intercept.pageSize).toNat
      if pageSize = 0 || pageSize ≥ 2 ^ 63 then
        throw (IO.userError "invalid page size")
      let state ← IO.mkRef {
        arch, verify, pageSize
        config := Prim.Intercept.seccompConfig arch
        layout := Prim.Intercept.registerLayout () : InterceptTrace.State }
      monitor.set (some (.trace state check))
    else
      let state ← IO.mkRef (← InterceptDso.prepare logOnly)
      monitor.set (some (.dso state check))
  catch _ =>
    throw (IO.userError "unable to initialize command interception")

private def stop : IO Unit := do
  let current ← monitor.swap none
  match current with
  | some (.trace state _) => InterceptTrace.close state
  | some (.dso state _) => InterceptDso.close (← state.get)
  | none => pure ()

structure Prepared where
  seccompFilter : ByteArray := ByteArray.empty
  trace : Bool := false
  env : Array String
  keepFds : Array UInt32 := #[]

def prepare (env : Array String) : IO Prepared := do
  match ← monitor.get with
  | some (.trace state _) =>
    return {
      seccompFilter := LeanSudo.Intercept.Seccomp.program (← state.get).config
      trace := true, env }
  | some (.dso state _) =>
    let state ← state.get
    return { env := InterceptDso.environment state env, keepFds := #[state.child] }
  | none => return { env }

def relayHooks : RelayHooks where
  onSpawn := fun pid => do
    match ← monitor.get with
    | some (.trace state _) => InterceptTrace.attach state pid
    | some (.dso state _) => InterceptDso.parent state
    | _ => pure ()
  onChild := fun pid status => do
    match ← monitor.get with
    | some (.trace state check) => InterceptTrace.childEvent state check pid status
    | _ => pure false
  onTick := do
    match ← monitor.get with
    | some (.dso state check) => InterceptDso.service state check
    | _ => pure ()
  onFinish := fun _ => do
    match ← monitor.get with
    | some (.trace state _) => InterceptTrace.close state
    | _ => pure ()

def withMonitor (trace verify logOnly : Bool) (check : Request → IO Bool)
    (action : IO α) : IO α := do
  start trace verify logOnly check
  try action finally stop

end LeanSudo.Sys.Intercept
