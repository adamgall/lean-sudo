namespace LeanSudo.Sys.GroupPlugin

/-- An initialized sudo group-provider ABI handle. Cleanup is explicit and also
performed by the external object's finalizer if IO exits exceptionally. -/
opaque HandlePointed : NonemptyType
def Handle : Type := HandlePointed.type
instance : Nonempty Handle := HandlePointed.property

/-- sudo separates the shared-object name and arguments at spaces/tabs only;
there is no shell expansion or second quoting layer. -/
def splitConfig (config : String) : String × Array String :=
  let words := config.splitOn "\t" |>.flatMap (·.splitOn " ")
  let name := words.headD ""
  let path := if name.startsWith "/" then name else "/usr/libexec/sudo/" ++ name
  (path, (words.drop 1 |>.filter (!·.isEmpty)).toArray)

@[extern "lean_sudo_group_plugin_load"]
private opaque loadRaw (path : @& String) (args : @& Array String) : IO (Option Handle)

/-- Loader errors are reported to the shell; init diagnostics come from the
plugin's sudo_printf callback. A failed init yields no queryable handle. -/
def load (config : String) : IO (Option Handle) :=
  let (path, args) := splitConfig config
  loadRaw path args

@[extern "lean_sudo_group_plugin_query"]
opaque query (handle : @& Handle) (user group : @& String) : IO Bool

@[extern "lean_sudo_group_plugin_close"]
opaque close (handle : @& Handle) : IO Unit

end LeanSudo.Sys.GroupPlugin
