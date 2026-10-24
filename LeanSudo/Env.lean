import LeanSudo.Policy.Types
import LeanSudo.Cli

/-!
# Command environment

A pure model of sudoers' `rebuild_env` / `validate_env_vars` / `insert_env_vars`
(plugins/sudoers/env.c) plus the PAM environment merge.

Two modes:
* **reset** (`env_reset`, or `-i`): start empty, keep only `env_check` variables with
  safe values and `env_keep` (and `PATH`) variables, then set `HOME`, `LOGNAME`, `USER`,
  `MAIL`, `SHELL`, `TERM`, `PATH`.
* **copy** (`!env_reset`, or `-E` with SETENV permission): copy the user's environment
  minus `env_delete` matches and `env_check` matches with unsafe values.

Bash function exports (values starting with `()`) and malformed names are always
dropped. `PATH` is forced to `secure_path` when set; `SUDO_COMMAND`, `SUDO_USER`,
`SUDO_UID`, `SUDO_GID` are always set last and cannot be overridden. The list never has
duplicate keys.

Proofs are in `LeanSudo.EnvProofs`.
-/

namespace LeanSudo

open LeanSudo.Cli (PreserveEnv)

abbrev EnvList := List (String × String)

structure EnvInput where
  /-- the invoking user's environment, in `environ` order -/
  userEnv : EnvList
  settings : Settings
  invoking : Principal
  target : Principal
  /-- value of `SUDO_COMMAND`: command path, then the arguments, space separated -/
  command : String
  preserve : PreserveEnv
  /-- SETENV tag / `setenv` default / command matched by `ALL` -/
  setenvAllowed : Bool
  /-- `sudo VAR=value cmd` -/
  cmdlineVars : EnvList
  /-- `-i` -/
  loginShell : Bool
  /-- `-H` -/
  setHome : Bool
  /-- environment returned by `pam_getenvlist` -/
  pamEnv : EnvList
  /-- `-s` (keeps the user's `SHELL` in reset mode; enables the `set_home` default) -/
  shellMode : Bool := false

/-! ## Primitive list operations -/

def hasKey (e : EnvList) (k : String) : Bool := e.any (fun kv => kv.1 == k)

def lookup (e : EnvList) (k : String) : Option String := (e.find? (fun kv => kv.1 == k)).map (·.2)

/-- Remove any existing binding of `k`, then append `(k, v)`. -/
def setVar (e : EnvList) (k v : String) : EnvList := e.filter (fun kv => kv.1 != k) ++ [(k, v)]

/-- Append `(k, v)` unless `k` is already bound. -/
def setDefault (e : EnvList) (k v : String) : EnvList := if hasKey e k then e else e ++ [(k, v)]

def setAll (e : EnvList) : EnvList → EnvList
  | [] => e
  | (k, v) :: rest => setAll (setVar e k v) rest

def addDefaults (e : EnvList) : EnvList → EnvList
  | [] => e
  | (k, v) :: rest => addDefaults (setDefault e k v) rest

/-! ## Variable classification -/

/-- sudo's env list patterns: exact name, or a prefix when the pattern ends in `*`. -/
def patMatchL : List Char → List Char → Bool
  | ['*'], _ => true
  | [], [] => true
  | p :: ps, c :: cs => p == c && patMatchL ps cs
  | _, _ => false

def patMatch (pat key : String) : Bool := patMatchL pat.toList key.toList

def matchesAny (pats : List String) (key : String) : Bool := pats.any (fun p => patMatch p key)

def validName (k : String) : Bool := !k.toList.isEmpty && !k.toList.contains '='

/-- Exported bash function (`NAME=() { ...; }`). -/
def isBashFn (v : String) : Bool :=
  match v.toList with
  | '(' :: ')' :: _ => true
  | _ => false

def entryOk (k v : String) : Bool := validName k && !isBashFn v

/-- A `..` path element (sudo's `tz_is_safe` loop, `last` starts as `/`). -/
def dotDotElem : Char → List Char → Bool
  | _, [] => false
  | last, c :: cs =>
    (last == '/' && c == '.' &&
      (match cs with
       | '.' :: r => r.isEmpty || r.head? == some '/'
       | _ => false)) || dotDotElem c cs

/-- sudo's `tz_is_safe`. -/
def tzSafe (v : String) : Bool :=
  let l := match v.toList with
    | ':' :: r => r
    | l => l
  (match l with
   | '/' :: _ => "/usr/share/zoneinfo/".toList.isPrefixOf l
   | _ => true) &&
  l.all (fun c => 0x20 < c.toNat && c.toNat < 0x7f) &&
  !dotDotElem '/' l && l.length < 4096

/-- `env_check` value test: no `%` or `/` (`TZ`: `tz_is_safe`). -/
def checkSafe (k v : String) : Bool :=
  if k == "TZ" then tzSafe v else !(v.toList.contains '%' || v.toList.contains '/')

/-- Kept in reset mode (sudo's `env_should_keep`; `PATH` is in sudo's built-in
`env_keep`, and `-s` keeps `SHELL`). -/
def keepReset (i : EnvInput) (k v : String) : Bool :=
  if matchesAny i.settings.envCheck k then checkSafe k v
  else matchesAny i.settings.envKeep k || k == "PATH" || (i.shellMode && k == "SHELL")

/-- Removed in copy mode (sudo's `env_should_delete`). -/
def deleteCopy (i : EnvInput) (k v : String) : Bool :=
  matchesAny i.settings.envDelete k || (matchesAny i.settings.envCheck k && !checkSafe k v)

/-- `-E` / `--preserve-env` without a list. -/
def wantsPreserveAll (i : EnvInput) : Bool :=
  match i.preserve with
  | .all => true
  | _ => false

/-- reset mode: `env_reset` (unless `-E`, which requires SETENV), or `-i`. -/
def resetMode (i : EnvInput) : Bool :=
  i.loginShell || (i.settings.envReset && !wantsPreserveAll i)

/-- A user variable survives the initial filtering. -/
def userPass (i : EnvInput) (reset : Bool) (k v : String) : Bool :=
  entryOk k v && (if reset then keepReset i k v else !deleteCopy i k v)

/-- A PAM variable is merged (only when its name is not already set). -/
def pamPass (i : EnvInput) (k v : String) : Bool :=
  entryOk k v && !matchesAny i.settings.envDelete k

/-- A `VAR=value` / `--preserve-env=VAR` variable may be set (sudo's
`validate_env_vars`; with SETENV anything but a bash function is allowed). -/
def extraAllowed (i : EnvInput) (reset : Bool) (k v : String) : Bool :=
  entryOk k v &&
    (i.setenvAllowed ||
      (!(i.settings.securePath.isSome && k == "PATH") &&
        (if reset then keepReset i k v else !deleteCopy i k v)))

/-- `--preserve-env=a,b` behaves like `a=$a b=$b` on the command line (sudo's
`parse_env_list`); unset variables are skipped. -/
def preserveExtra (i : EnvInput) : EnvList :=
  match i.preserve with
  | .vars vs => vs.filterMap fun n => (i.userEnv.find? (fun kv => kv.1 == n)).map fun kv => (n, kv.2)
  | _ => []

def extraVars (i : EnvInput) : EnvList := i.cmdlineVars ++ preserveExtra i

/-! ## Construction -/

def stdPath : String := "/usr/bin:/bin:/usr/sbin:/sbin"
def loginPath : String := "/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin"

/-- `HOME` is reset to the target's home directory. -/
def resetHome (i : EnvInput) : Bool :=
  i.settings.alwaysSetHome || i.setHome || i.loginShell || (i.shellMode && i.settings.setHome)

def baseEnv (i : EnvInput) (reset : Bool) : EnvList :=
  setAll [] (i.userEnv.filter fun kv => userPass i reset kv.1 kv.2)

/-- `LOGNAME`/`USER` in reset mode without `-i` (sudo's `set_logname` handling: set both
to the target unless preserved; if only one was preserved, copy it to the other). -/
def lognameReset (i : EnvInput) (e : EnvList) : EnvList :=
  match lookup e "LOGNAME", lookup e "USER" with
  | none, none => setVar (setVar e "LOGNAME" i.target.name) "USER" i.target.name
  | some l, none => setVar e "USER" l
  | none, some u => setVar e "LOGNAME" u
  | some _, some _ => e

def defaultsReset (i : EnvInput) (e : EnvList) : EnvList :=
  let e1 := if i.loginShell then
      setVar (setVar (setVar e "SHELL" i.target.shell) "LOGNAME" i.target.name) "USER" i.target.name
    else lognameReset i e
  let e2 := if i.loginShell || !hasKey e "MAIL" then setVar e1 "MAIL" ("/var/mail/" ++ i.target.name)
    else e1
  if resetHome i || !hasKey e "HOME" then setVar e2 "HOME" i.target.home else e2

def defaultsCopy (i : EnvInput) (e : EnvList) : EnvList :=
  let e1 := setVar (setVar e "LOGNAME" i.target.name) "USER" i.target.name
  if resetHome i then setVar e1 "HOME" i.target.home else e1

def commonDefaults (i : EnvInput) (e : EnvList) : EnvList :=
  let e1 := setDefault e "SHELL" i.target.shell
  let e2 := setDefault e1 "TERM" "unknown"
  let e3 := if i.loginShell then setVar e2 "PATH" loginPath else setDefault e2 "PATH" stdPath
  match lookup (i.userEnv.filter fun kv => entryOk kv.1 kv.2) "SUDO_PS1" with
  | some ps1 => setVar e3 "PS1" ps1
  | none => e3

def applySecurePath (i : EnvInput) (e : EnvList) : EnvList :=
  match i.settings.securePath with
  | some p => setVar e "PATH" p
  | none => e

def sudoVars (i : EnvInput) (e : EnvList) : EnvList :=
  setVar (setVar (setVar (setVar e "SUDO_COMMAND" i.command) "SUDO_USER" i.invoking.name)
    "SUDO_UID" (toString i.invoking.uid)) "SUDO_GID" (toString i.invoking.gid)

def pamVars (i : EnvInput) : EnvList := i.pamEnv.filter fun kv => pamPass i kv.1 kv.2

def assemble (i : EnvInput) (reset : Bool) (extra : EnvList) : EnvList :=
  let e0 := baseEnv i reset
  let e1 := if reset then defaultsReset i e0 else defaultsCopy i e0
  let e2 := commonDefaults i e1
  let e3 := setAll e2 extra
  let e4 := applySecurePath i e3
  let e5 := sudoVars i e4
  addDefaults e5 (pamVars i)

def preserveDeniedMsg : String := "sorry, you are not allowed to preserve the environment"

/-- Build the command's environment. -/
def buildEnv (i : EnvInput) : Except String EnvList :=
  if wantsPreserveAll i && !i.setenvAllowed then .error preserveDeniedMsg
  else
    let reset := resetMode i
    let extra := extraVars i
    let bad := extra.filter fun kv => !extraAllowed i reset kv.1 kv.2
    if bad.isEmpty then .ok (assemble i reset extra)
    else .error ("sorry, you are not allowed to set the following environment variables: " ++
      String.intercalate ", " (bad.map (·.1)))

/-- `KEY=VALUE` strings for `execve`. -/
def envToArray (e : EnvList) : Array String := (e.map fun kv => kv.1 ++ "=" ++ kv.2).toArray

/-- Keys sudo itself may set. -/
def sudoKeys : List String :=
  ["HOME", "LOGNAME", "USER", "MAIL", "SHELL", "TERM", "PATH", "PS1",
   "SUDO_COMMAND", "SUDO_USER", "SUDO_UID", "SUDO_GID"]

end LeanSudo
