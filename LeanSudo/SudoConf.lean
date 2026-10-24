namespace LeanSudo.SudoConf

/-- Front-end configuration is separate from the sudoers policy. Unknown plugins
must never silently fall back to sudoers: an approval plugin may restrict access. -/
structure Config where
  askpass : Option String := none
  noexec : Option String := some "/usr/libexec/sudo/sudo_noexec.so"
  devsearch : String := "/dev/pts:/dev/vt:/dev/term:/dev/zcons:/dev/pty:/dev"
  disableCoredump : Bool := true
  groupSource : String := "adaptive"
  maxGroups : Nat := 65536
  probeInterfaces : Bool := true
  deriving BEq, Repr, Inhabited

def supportedPlugin (symbol path : String) (args : List String) : Bool :=
  ["sudoers_policy", "sudoers_io", "sudoers_audit"].contains symbol &&
    (path == "sudoers.so" || path == "/usr/libexec/sudo/sudoers.so" ||
      path == "/usr/lib/sudo/sudoers.so") && args.isEmpty

private def boolean (s : String) : Except String Bool :=
  if ["true", "yes", "on", "1"].contains s.toLower then .ok true
  else if ["false", "no", "off", "0"].contains s.toLower then .ok false
  else .error ("invalid boolean value: " ++ s)

private def line (c : Config) (words : List String) : Except String Config := do
  let words := match words with
    | name :: rest =>
      let directive := if name.toLower == "plugin" then "Plugin"
        else if name.toLower == "path" then "Path"
        else if name.toLower == "set" then "Set"
        else if name.toLower == "debug" then "Debug" else name
      directive :: (if directive == "Path" then
        match rest with | key :: xs => key.toLower :: xs | [] => [] else rest)
    | [] => []
  match words with
  | [] => return c
  | "Plugin" :: symbol :: path :: args =>
    if supportedPlugin symbol path args then return c
    else throw ("unable to load plugin " ++ symbol ++ ": unsupported sudo.conf plugin configuration")
  | ["Path", "askpass", value] => return { c with askpass := some value }
  | ["Path", "noexec", value] => return { c with noexec := some value }
  | ["Path", "devsearch", value] => return { c with devsearch := value }
  | ["Path", "askpass"] => return { c with askpass := none }
  | ["Path", "noexec"] => return { c with noexec := none }
  | ["Path", "devsearch"] => return { c with devsearch := "" }
  | "Path" :: _ :: _ => return c
  | ["Set", "disable_coredump", value] =>
    return { c with disableCoredump := ← boolean value }
  | ["Set", "probe_interfaces", value] =>
    return { c with probeInterfaces := ← boolean value }
  | ["Set", "group_source", value] =>
    if ["adaptive", "static", "dynamic"].contains value.toLower then
      return { c with groupSource := value.toLower }
    else throw ("invalid group source: " ++ value)
  | ["Set", "max_groups", value] =>
    match value.toNat? with
    | some n => if n > 0 && n ≤ 1024 then return { c with maxGroups := n } else throw "invalid max_groups"
    | none => throw "invalid max_groups"
  | "Debug" :: _ => return c
  | ["Set", "developer_mode", _] => return c
  | "Plugin" :: _ => throw "invalid sudo.conf Plugin directive"
  | _ => return c

/-- Parse physical lines after joining backslash continuations and stripping comments. -/
def parse (text : String) : Except String Config := do
  let lines := (text.replace "\\\n" "").splitOn "\n"
  lines.foldlM (fun c s =>
    line c (((s.splitOn "#").headD "").splitOn " " |>.flatMap (·.splitOn "\t")
      |>.map (·.trimAscii.toString) |>.filter (!·.isEmpty))) {}

/-- Extra arguments can change plugin semantics and cannot be silently discarded. -/
theorem plugin_arguments_refused (symbol path : String) (arg : String) (args : List String) :
    supportedPlugin symbol path (arg :: args) = false := by
  simp [supportedPlugin]

/-- No plugin outside the built-in sudoers trio can be silently bypassed. -/
theorem unknown_plugin_refused (symbol path : String) (args : List String)
    (h : ["sudoers_policy", "sudoers_io", "sudoers_audit"].contains symbol = false) :
    supportedPlugin symbol path args = false := by
  unfold supportedPlugin
  rw [h]
  rfl

end LeanSudo.SudoConf
