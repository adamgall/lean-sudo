import LeanSudo
import LeanSudo.Sys.PamHelpers
import LeanSudo.Sys.Lookup
import LeanSudo.Background

def main (args : List String) : IO UInt32 := do
  LeanSudo.Sys.registerExecHelpers
  LeanSudo.Sys.Edit.registerHelper
  LeanSudo.Sys.Lookup.register
  LeanSudo.Sys.PamHelpers.register
  LeanSudo.Helper.register "logsrv-resolve" LeanSudo.Sys.LogSrv.resolverHelper
  LeanSudo.Background.register LeanSudo.Shell.run
  if let some status ← LeanSudo.Helper.dispatch args then return status
  try
    if let some status ← LeanSudo.Background.launchIfRequested args then return status
  catch error =>
    LeanSudo.Sys.writeStderr s!"sudo: {error}\n"
    return 1
  LeanSudo.Shell.run args
