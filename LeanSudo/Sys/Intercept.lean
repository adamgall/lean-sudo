namespace LeanSudo.Sys.Intercept

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

def withMonitor (trace verify logOnly : Bool) (check : Request → IO Bool)
    (action : IO α) : IO α := do
  start trace verify logOnly check
  try action finally stop

end LeanSudo.Sys.Intercept
