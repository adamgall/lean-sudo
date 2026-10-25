namespace LeanSudo.Sys.GroupPlugin

opaque HandlePointed : NonemptyType
def Handle : Type := HandlePointed.type
instance : Nonempty Handle := HandlePointed.property

def splitConfig (config : String) : String × Array String :=
  let words := config.splitOn "\t" |>.flatMap (·.splitOn " ")
  let name := words.headD ""
  let path := if name.startsWith "/" then name else "/usr/libexec/sudo/" ++ name
  (path, (words.drop 1 |>.filter (!·.isEmpty)).toArray)

@[extern "lean_sudo_group_plugin_load"]
private opaque loadRaw (path : @& String) (args : @& Array String) : IO (Option Handle)

def load (config : String) : IO (Option Handle) :=
  let (path, args) := splitConfig config
  loadRaw path args

@[extern "lean_sudo_group_plugin_query"]
opaque query (handle : @& Handle) (user group : @& String) : IO Bool

@[extern "lean_sudo_group_plugin_close"]
opaque close (handle : @& Handle) : IO Unit

end LeanSudo.Sys.GroupPlugin
