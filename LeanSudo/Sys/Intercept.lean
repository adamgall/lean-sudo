namespace LeanSudo.Sys.Intercept

/-- Kernel/DSO facts, not authorization. Identities are deliberately absent. -/
structure Request where
  command : String
  cwd : String
  argv : Array String
  env : Array String
  pid : UInt32
  setid : Bool
  deriving Repr

@[extern "lean_sudo_intercept_start"]
private opaque start (trace verify logOnly : Bool) (check : Request → IO Bool) : IO Unit

@[extern "lean_sudo_intercept_stop"]
private opaque stop : IO Unit

/-- A separate privileged broker owns the Lean policy closure. Each monitored
exec uses a private reply socket; an absent or invalid response cannot allow it. -/
def withMonitor (trace verify logOnly : Bool) (check : Request → IO Bool)
    (action : IO α) : IO α := do
  start trace verify logOnly check
  try action finally stop

end LeanSudo.Sys.Intercept
