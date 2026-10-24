import LeanSudo.Policy.Types
import LeanSudo.Cli

/-!
# Command environment

A pure model of sudoers' `rebuild_env` / `validate_env_vars` / `insert_env_vars`
(plugins/sudoers/env.c) plus the PAM environment merge.

Two modes:
* **reset** (`env_reset`, or `-i`): start empty, keep only `env_check` variables with
  safe values and `env_keep` variables (including `PATH` in the default list),
  then supply defaults for `HOME`, `LOGNAME`, `USER`, `MAIL`, `SHELL`, `TERM`, `PATH`.
* **copy** (`!env_reset`, or `-E` with SETENV permission): copy the user's environment
  minus `env_delete` matches and `env_check` matches with unsafe values.

Malformed names are dropped. User entries follow the name/value patterns and bash
function rules of `env.c`. `secure_path` (unless exempt) and the invoking identity
are installed during rebuilding, then authorized explicit assignments overwrite
them. Trusted PAM entries merge last, overwriting entries not kept by policy.
The list never has duplicate keys.

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
  /-- Ordered `VAR=value` assignments and snapshots of set `--preserve-env=list`
  variables, resolved by the CLI at their position among the arguments. -/
  cmdlineVars : EnvList
  /-- `-i` -/
  loginShell : Bool
  /-- `-H` -/
  setHome : Bool
  /-- environment returned by `pam_getenvlist` -/
  pamEnv : EnvList
  /-- `-s` (keeps the user's `SHELL` in reset mode; enables the `set_home` default) -/
  shellMode : Bool := false
  ttyName : Option String := none
  envFile : EnvList := []
  restrictedEnvFile : EnvList := []
  /-- Real invoking gid, which may differ from passwd's primary gid after newgrp. -/
  invokingRealGid : Option Nat := none

/-- sudo's exempt_group bypasses authentication and secure_path, not authorization. -/
def userIsExempt (settings : Settings) (user : Principal) : Bool :=
  settings.exemptGroup.any fun name => user.groups.any (fun g => g.1 == name)

def effectiveSecurePath (i : EnvInput) : Option String :=
  if userIsExempt i.settings i.invoking then none else i.settings.securePath

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

/-- `env_pattern.c` uses the first occurrence of the character after `*`, without
backtracking. A wildcard cannot cross the name/value separator unless its next
literal is `=`. The result records whether a value character was matched
explicitly (a final `*` alone does not make a full match). -/
def envPatternL : List Char → List Char → Bool → Bool → Option Bool
  | [], cs, inValue, full =>
    if cs.isEmpty || (!inValue && cs.head? == some '=') then some full else none
  | ['*'], _, _, full => some full
  | '*' :: '*' :: ps, cs, inValue, full => envPatternL ('*' :: ps) cs inValue full
  | '*' :: p :: ps, cs, inValue, full =>
    let rest := cs.dropWhile fun c => c != p && (inValue || p == '=' || c != '=')
    match rest with
    | c :: cs =>
      if p == c then envPatternL ps cs (inValue || p == '=') (full || inValue) else none
    | [] => none
  | p :: ps, c :: cs, inValue, full =>
    if p == c then envPatternL ps cs (inValue || p == '=') (full || inValue) else none
  | _, _, _, _ => none

def patMatchL (pat value : List Char) : Bool :=
  (envPatternL pat value false false).isSome

def patMatch (pat value : String) : Bool := patMatchL pat.toList value.toList

/-- Linux sudo treats LOGNAME and USER as the same name-only entry, even for
value-qualified patterns: `USER=alice` matches neither identity variable. -/
def entryPattern (pat k v : String) : Option Bool :=
  if k == "LOGNAME" || k == "USER" then
    (envPatternL pat.toList "LOGNAME".toList false false).orElse fun _ =>
      envPatternL pat.toList "USER".toList false false
  else envPatternL pat.toList (k ++ "=" ++ v).toList false false

def matchesAny (pats : List String) (k v : String) : Bool :=
  pats.any fun p => (entryPattern p k v).isSome

/-- The first matching pattern supplies `full_match`, as in `matches_env_list`. -/
def matchFull : List String → String → String → Bool
  | [], _, _ => false
  | p :: ps, k, v =>
    match entryPattern p k v with
    | some full => full
    | none => matchFull ps k v

def validName (k : String) : Bool := !k.toList.isEmpty && !k.toList.contains '='

/-- Function prefix rejected by `env_should_keep` unless the value is matched. -/
def isBashFn (v : String) : Bool :=
  match v.toList with
  | '(' :: ')' :: ' ' :: _ => true
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

/-- Whitelist classification before the function-export full-match check. -/
def keepResetPolicy (i : EnvInput) (k v : String) : Bool :=
  if matchesAny i.settings.envCheck k v then checkSafe k v
  else matchesAny i.settings.envKeep k v || (i.shellMode && k == "SHELL")

/-- `env_should_keep`: `env_check` wins over `env_keep`; function exports require
a pattern matching the value, not just the name. `-s` implicitly keeps SHELL. -/
def keepReset (i : EnvInput) (k v : String) : Bool :=
  keepResetPolicy i k v &&
    (!isBashFn v || (if matchesAny i.settings.envCheck k v then
      matchFull i.settings.envCheck k v
    else if i.shellMode && k == "SHELL" then false else matchFull i.settings.envKeep k v))

/-- Removed in copy mode (sudo's `env_should_delete`). -/
def deleteCopy (i : EnvInput) (k v : String) : Bool :=
  matchesAny i.settings.envDelete k v || (matchesAny i.settings.envCheck k v && !checkSafe k v)

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
  validName k && (if reset then keepReset i k v else !deleteCopy i k v)

/-- PAM is a trusted source, not user input: no env_delete or function filtering. -/
def pamPass (_i : EnvInput) (k _v : String) : Bool := validName k

/-- A `VAR=value` / `--preserve-env=VAR` variable may be set (sudo's
`validate_env_vars`; SETENV bypasses the environment policy checks). -/
def extraAllowed (i : EnvInput) (reset : Bool) (k v : String) : Bool :=
  validName k &&
    (i.setenvAllowed ||
      (!((effectiveSecurePath i).isSome && k == "PATH") &&
        (if reset then keepReset i k v else !deleteCopy i k v)))

/-- Both forms of explicit assignment were materialized in encounter order by
the CLI; `preserve.vars` is metadata, not a second insertion pass. -/
def extraVars (i : EnvInput) : EnvList := i.cmdlineVars

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
    else if i.settings.setLogname then lognameReset i e
    else setDefault (setDefault e "LOGNAME" i.invoking.name) "USER" i.invoking.name
  let e2 := if i.loginShell || !hasKey e "MAIL" then setVar e1 "MAIL" ("/var/mail/" ++ i.target.name)
    else e1
  if resetHome i || !hasKey e "HOME" then setVar e2 "HOME" i.target.home else e2

def defaultsCopy (i : EnvInput) (e : EnvList) : EnvList :=
  let e1 := if i.settings.setLogname then setVar (setVar e "LOGNAME" i.target.name) "USER" i.target.name else e
  if resetHome i then setVar e1 "HOME" i.target.home else e1

def commonDefaults (i : EnvInput) (e : EnvList) : EnvList :=
  let e1 := setDefault e "SHELL" i.target.shell
  let e2 := setDefault e1 "TERM" "unknown"
  let e3 := setDefault e2 "PATH" stdPath
  match lookup (i.userEnv.filter fun kv => entryOk kv.1 kv.2) "SUDO_PS1" with
  | some ps1 => setVar e3 "PS1" ps1
  | none => e3

def applySecurePath (i : EnvInput) (e : EnvList) : EnvList :=
  match effectiveSecurePath i with
  | some p => setVar e "PATH" p
  | none => e

def sudoVars (i : EnvInput) (e : EnvList) : EnvList :=
  let e := setVar e "SUDO_HOME" i.invoking.home
  let e := match i.ttyName with
    | some tty => setVar e "SUDO_TTY" tty
    | none => e.filter (fun kv => kv.1 != "SUDO_TTY")
  setVar (setVar (setVar (setVar e "SUDO_COMMAND" i.command) "SUDO_USER" i.invoking.name)
    "SUDO_UID" (toString i.invoking.uid)) "SUDO_GID" (toString (i.invokingRealGid.getD i.invoking.gid))

def pamVars (i : EnvInput) : EnvList := i.pamEnv.filter fun kv => pamPass i kv.1 kv.2

/-- `env_merge` tests the incoming PAM value, not the existing binding. -/
def pamOverwrite (i : EnvInput) (k v : String) : Bool :=
  if resetMode i then !keepReset i k v else deleteCopy i k v

def mergePam (i : EnvInput) (e : EnvList) : EnvList → EnvList
  | [] => e
  | (k, v) :: rest =>
    mergePam i (if pamOverwrite i k v then setVar e k v else setDefault e k v) rest

/-- Administrator-supplied files do not overwrite existing environment entries. -/
def fileVars (i : EnvInput) : EnvList :=
  ((i.restrictedEnvFile.filter fun kv => userPass i (resetMode i) kv.1 kv.2) ++
    (i.envFile.filter fun kv => entryOk kv.1 kv.2)).filter (fun kv => kv.1 != "SUDO_TTY")

def assemble (i : EnvInput) (reset : Bool) (extra : EnvList) : EnvList :=
  let e0 := baseEnv i reset
  let e1 := if reset then defaultsReset i e0 else defaultsCopy i e0
  let e2 := commonDefaults i e1
  let e3 := applySecurePath i e2
  let e4 := sudoVars i e3
  let e5 := addDefaults e4 (fileVars i)
  let e6 := setAll e5 extra
  mergePam i e6 (pamVars i)

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
   "SUDO_COMMAND", "SUDO_USER", "SUDO_UID", "SUDO_GID", "SUDO_HOME", "SUDO_TTY"]

end LeanSudo
