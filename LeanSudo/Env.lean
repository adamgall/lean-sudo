import LeanSudo.Policy.Types
import LeanSudo.Cli

namespace LeanSudo

open LeanSudo.Cli (PreserveEnv)

abbrev EnvList := List (String × String)

structure EnvInput where
  userEnv : EnvList
  settings : Settings
  invoking : Principal
  target : Principal
  command : String
  preserve : PreserveEnv
  setenvAllowed : Bool
  cmdlineVars : EnvList
  loginShell : Bool
  setHome : Bool
  pamEnv : EnvList
  shellMode : Bool := false
  ttyName : Option String := none
  envFile : EnvList := []
  restrictedEnvFile : EnvList := []
  invokingRealGid : Option Nat := none

def userIsExempt (settings : Settings) (user : Principal) : Bool :=
  settings.exemptGroup.any fun name => user.groups.any (fun g => g.1 == name)

def effectiveSecurePath (i : EnvInput) : Option String :=
  if userIsExempt i.settings i.invoking then none else i.settings.securePath

def hasKey (e : EnvList) (k : String) : Bool := e.any (fun kv => kv.1 == k)

def lookup (e : EnvList) (k : String) : Option String := (e.find? (fun kv => kv.1 == k)).map (·.2)

def setVar (e : EnvList) (k v : String) : EnvList := e.filter (fun kv => kv.1 != k) ++ [(k, v)]

def setDefault (e : EnvList) (k v : String) : EnvList := if hasKey e k then e else e ++ [(k, v)]

def setAll (e : EnvList) : EnvList → EnvList
  | [] => e
  | (k, v) :: rest => setAll (setVar e k v) rest

def addDefaults (e : EnvList) : EnvList → EnvList
  | [] => e
  | (k, v) :: rest => addDefaults (setDefault e k v) rest

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

def entryPattern (pat k v : String) : Option Bool :=
  if k == "LOGNAME" || k == "USER" then
    (envPatternL pat.toList "LOGNAME".toList false false).orElse fun _ =>
      envPatternL pat.toList "USER".toList false false
  else envPatternL pat.toList (k ++ "=" ++ v).toList false false

def matchesAny (pats : List String) (k v : String) : Bool :=
  pats.any fun p => (entryPattern p k v).isSome

def matchFull : List String → String → String → Bool
  | [], _, _ => false
  | p :: ps, k, v =>
    match entryPattern p k v with
    | some full => full
    | none => matchFull ps k v

def validName (k : String) : Bool := !k.toList.isEmpty && !k.toList.contains '='

def isBashFn (v : String) : Bool :=
  match v.toList with
  | '(' :: ')' :: ' ' :: _ => true
  | _ => false

def entryOk (k v : String) : Bool := validName k && !isBashFn v

def dotDotElem : Char → List Char → Bool
  | _, [] => false
  | last, c :: cs =>
    (last == '/' && c == '.' &&
      (match cs with
       | '.' :: r => r.isEmpty || r.head? == some '/'
       | _ => false)) || dotDotElem c cs

def tzSafe (v : String) : Bool :=
  let l := match v.toList with
    | ':' :: r => r
    | l => l
  (match l with
   | '/' :: _ => "/usr/share/zoneinfo/".toList.isPrefixOf l
   | _ => true) &&
  l.all (fun c => 0x20 < c.toNat && c.toNat < 0x7f) &&
  !dotDotElem '/' l && l.length < 4096

def checkSafe (k v : String) : Bool :=
  if k == "TZ" then tzSafe v else !(v.toList.contains '%' || v.toList.contains '/')

def keepResetPolicy (i : EnvInput) (k v : String) : Bool :=
  if matchesAny i.settings.envCheck k v then checkSafe k v
  else matchesAny i.settings.envKeep k v || (i.shellMode && k == "SHELL")

def keepReset (i : EnvInput) (k v : String) : Bool :=
  keepResetPolicy i k v &&
    (!isBashFn v || (if matchesAny i.settings.envCheck k v then
      matchFull i.settings.envCheck k v
    else if i.shellMode && k == "SHELL" then false else matchFull i.settings.envKeep k v))

def deleteCopy (i : EnvInput) (k v : String) : Bool :=
  matchesAny i.settings.envDelete k v || (matchesAny i.settings.envCheck k v && !checkSafe k v)

def wantsPreserveAll (i : EnvInput) : Bool :=
  match i.preserve with
  | .all => true
  | _ => false

def resetMode (i : EnvInput) : Bool :=
  i.loginShell || (i.settings.envReset && !wantsPreserveAll i)

def userPass (i : EnvInput) (reset : Bool) (k v : String) : Bool :=
  validName k && (if reset then keepReset i k v else !deleteCopy i k v)

def pamPass (_i : EnvInput) (k _v : String) : Bool := validName k

def extraAllowed (i : EnvInput) (reset : Bool) (k v : String) : Bool :=
  validName k &&
    (i.setenvAllowed ||
      (!((effectiveSecurePath i).isSome && k == "PATH") &&
        (if reset then keepReset i k v else !deleteCopy i k v)))

def extraVars (i : EnvInput) : EnvList := i.cmdlineVars

def stdPath : String := "/usr/bin:/bin:/usr/sbin:/sbin"
def loginPath : String := "/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin"

def resetHome (i : EnvInput) : Bool :=
  i.settings.alwaysSetHome || i.setHome || i.loginShell || (i.shellMode && i.settings.setHome)

def baseEnv (i : EnvInput) (reset : Bool) : EnvList :=
  setAll [] (i.userEnv.filter fun kv => userPass i reset kv.1 kv.2)

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

def pamOverwrite (i : EnvInput) (k v : String) : Bool :=
  if resetMode i then !keepReset i k v else deleteCopy i k v

def mergePam (i : EnvInput) (e : EnvList) : EnvList → EnvList
  | [] => e
  | (k, v) :: rest =>
    mergePam i (if pamOverwrite i k v then setVar e k v else setDefault e k v) rest

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

def buildEnv (i : EnvInput) : Except String EnvList :=
  if wantsPreserveAll i && !i.setenvAllowed then .error preserveDeniedMsg
  else
    let reset := resetMode i
    let extra := extraVars i
    let bad := extra.filter fun kv => !extraAllowed i reset kv.1 kv.2
    if bad.isEmpty then .ok (assemble i reset extra)
    else .error ("sorry, you are not allowed to set the following environment variables: " ++
      String.intercalate ", " (bad.map (·.1)))

def envToArray (e : EnvList) : Array String := (e.map fun kv => kv.1 ++ "=" ++ kv.2).toArray

def sudoKeys : List String :=
  ["HOME", "LOGNAME", "USER", "MAIL", "SHELL", "TERM", "PATH", "PS1",
   "SUDO_COMMAND", "SUDO_USER", "SUDO_UID", "SUDO_GID", "SUDO_HOME", "SUDO_TTY"]

end LeanSudo
