namespace LeanSudo.SudoConf

structure Plugin where
  symbol : String
  path : String
  options : List String := []
  line : Nat
  deriving BEq, Repr, Inhabited

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
  pluginDir : String := "/usr/libexec/sudo/"
  plugins : List Plugin := []
  deriving BEq, Repr, Inhabited

def supportedPlugin (symbol path : String) (args : List String) : Bool :=
  ["sudoers_policy", "sudoers_io", "sudoers_audit"].contains symbol &&
    (path == "sudoers.so" || path == "/usr/libexec/sudo/sudoers.so" ||
      path == "/usr/lib/sudo/sudoers.so") && args.isEmpty

private def boolean (s : String) : Except String Bool :=
  if ["true", "yes", "on", "1"].contains s.toLower then .ok true
  else if ["false", "no", "off", "0"].contains s.toLower then .ok false
  else .error ("invalid boolean value: " ++ s)

private def line (c : Config) (lineno : Nat) (words : List String) : Except String Config := do
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
    if supportedPlugin symbol path args then
      return { c with plugins := c.plugins ++ [{ symbol, path, options := args, line := lineno }] }
    else if symbol == "sudoers_policy" && path == "sudoers.so" then
      throw ("unable to load plugin " ++ symbol ++ ": unsupported sudo.conf plugin configuration")
    else return { c with plugins := c.plugins ++ [{ symbol, path, options := args, line := lineno }] }
  | ["Path", "askpass", value] => return { c with askpass := some value }
  | ["Path", "noexec", value] => return { c with noexec := some value }
  | ["Path", "devsearch", value] => return { c with devsearch := value }
  | ["Path", "askpass"] => return { c with askpass := none }
  | ["Path", "noexec"] => return { c with noexec := none }
  | ["Path", "devsearch"] => return { c with devsearch := "" }
  | ["Path", "plugin_dir", value] =>
    return { c with pluginDir := value }
  | ["Path", "plugin_dir"] => return { c with pluginDir := "" }
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
  let (n, pending, c) ← (text.splitOn "\n").foldlM
    (fun (n, pending, c) s => do
      let s := String.ofList ((s.toList.reverse.dropWhile (· == '\r')).reverse)
      let parts := s.splitOn "#"
      let s := parts.headD ""
      if parts.length == 1 && s.endsWith "\\" && !s.endsWith "\\\\" then
        pure (n + 1, pending ++ (s.dropEnd 1).toString, c)
      else
        let words := (pending ++ s).splitOn " "
          |>.flatMap (·.splitOn "\t") |>.filter (!·.isEmpty)
        let c ← line c n words
        pure (n + 1, "", c))
    (1, "", ({} : Config))
  if pending.isEmpty then return c
  line c (n - 1) (pending.splitOn " " |>.flatMap (·.splitOn "\t") |>.filter (!·.isEmpty))

/-- sudo.conf uses sudo_secure_fd with uid 0 and no trusted group: even
root-group write permission is rejected. Diagnostic precedence matches sudo. -/
def fileProblem (uid mode : Nat) : Option String :=
  if mode &&& 0o170000 != 0o100000 then some "is not a regular file"
  else if uid != 0 then some s!"is owned by uid {uid}, should be 0"
  else if mode &&& 0o002 != 0 then some "is world writable"
  else if mode &&& 0o020 != 0 then some "is group writable"
  else none

/-- An insecure front-end configuration is ignored, not parsed. This differs
from the deliberately fatal handling of insecure sudoers policy files. -/
def parseFile (uid mode : Nat) (text : String) : Except String Config :=
  match fileProblem uid mode with
  | some _ => .ok {}
  | none => parse text

theorem insecure_file_uses_defaults (uid mode : Nat) (text problem : String)
    (h : fileProblem uid mode = some problem) :
    parseFile uid mode text = .ok {} := by
  simp [parseFile, h]

/-- Built-in emulation must not silently discard arguments; such lines require
the host's explicit handling rather than bypassing plugin initialization. -/
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
