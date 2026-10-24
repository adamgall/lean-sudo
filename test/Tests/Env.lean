import LeanSudo.Env
import LeanSudo.EnvProofs

/-! Compile-time tests for `LeanSudo.Env`. -/

namespace Tests.Env

open LeanSudo

def alice : Principal :=
  { name := "alice", uid := 1000, gid := 100, groups := [("users", 100)], home := "/home/alice",
    shell := "/bin/zsh" }

def root : Principal :=
  { name := "root", uid := 0, gid := 0, groups := [("root", 0)], home := "/root", shell := "/bin/bash" }

def userEnv : EnvList :=
  [("HOME", "/home/alice"), ("PATH", "/home/alice/bin:/usr/bin"), ("TERM", "xterm"),
   ("LANG", "en_US.UTF-8"), ("LC_ALL", "C/../x"), ("LD_PRELOAD", "/tmp/evil.so"),
   ("LD_LIBRARY_PATH", "/tmp"), ("DISPLAY", ":0"), ("FOO", "bar"),
   ("BASH_FUNC_x%%", "() { id; }"), ("TZ", "Europe/Paris"), ("MAIL", "/var/mail/alice"),
   ("SHELL", "/bin/zsh"), ("SUDO_PS1", "# "), ("=bad", "x"), ("IFS", " "),
   ("LOGNAME", "alice"), ("USER", "alice")]

def base : EnvInput :=
  { userEnv, settings := {}, invoking := alice, target := root, command := "/usr/bin/id -u",
    preserve := .none, setenvAllowed := false, cmdlineVars := [], loginShell := false,
    setHome := false, pamEnv := [] }

def run (i : EnvInput) : Option EnvList :=
  match buildEnv i with
  | .ok e => some e
  | .error _ => none

def err (i : EnvInput) : Option String :=
  match buildEnv i with
  | .ok _ => none
  | .error e => some e

def get (i : EnvInput) (k : String) : Option String := (run i).bind (lookup · k)

def sudoTail : EnvList :=
  [("SUDO_HOME", "/home/alice"), ("SUDO_COMMAND", "/usr/bin/id -u"), ("SUDO_USER", "alice"), ("SUDO_UID", "1000"),
   ("SUDO_GID", "100")]

/-! ### env_reset (default) -/
#guard run base == some ([("PATH", "/home/alice/bin:/usr/bin"), ("TERM", "xterm"),
  ("LANG", "en_US.UTF-8"), ("DISPLAY", ":0"), ("TZ", "Europe/Paris"),
  ("LOGNAME", "root"), ("USER", "root"), ("MAIL", "/var/mail/root"), ("HOME", "/root"),
  ("SHELL", "/bin/bash"), ("PS1", "# ")] ++ sudoTail)

-- secure_path replaces PATH, once
#guard get { base with settings := { securePath := some "/usr/sbin:/usr/bin" } } "PATH" ==
  some "/usr/sbin:/usr/bin"
#guard ((run { base with settings := { securePath := some "/sbin" } }).getD []).filter
  (·.1 == "PATH") == [("PATH", "/sbin")]
#guard get { base with settings := { securePath := some "/sbin", exemptGroup := some "users" } } "PATH" ==
  some "/home/alice/bin:/usr/bin"
#guard get { base with settings := { securePath := some "/sbin", exemptGroup := some "other" } } "PATH" ==
  some "/sbin"
#guard get { base with invokingRealGid := some 4 } "SUDO_GID" == some "4"

-- env_keep wildcard and exact names
#guard get { base with settings := { envKeep := ["FO*"] } } "FOO" == some "bar"
#guard get { base with settings := { envKeep := ["FO"] } } "FOO" == none
#guard get { base with settings := { envKeep := ["LD_*"] } } "LD_PRELOAD" == some "/tmp/evil.so"
#guard get base "LD_PRELOAD" == none
#guard get base "LD_LIBRARY_PATH" == none
#guard get base "FOO" == none
#guard get base "IFS" == none

-- env_keep'd HOME / MAIL / LOGNAME are preserved unless -H / always_set_home / -i
#guard get { base with settings := { envKeep := ["HOME", "MAIL"] } } "HOME" == some "/home/alice"
#guard get { base with settings := { envKeep := ["HOME", "MAIL"] } } "MAIL" == some "/var/mail/alice"
#guard get { base with settings := { envKeep := ["HOME"] }, setHome := true } "HOME" == some "/root"
#guard get { base with settings := { envKeep := ["HOME"], alwaysSetHome := true } } "HOME" == some "/root"
#guard get { base with settings := { envKeep := ["LOGNAME"] } } "USER" == some "alice"

-- env_check: values with % or / are dropped; TZ uses tz_is_safe
#guard get base "LC_ALL" == none
#guard get { base with userEnv := [("TERM", "vt100%n")] } "TERM" == some "unknown"
#guard get { base with userEnv := [("LANG", "C")] } "LANG" == some "C"
#guard get { base with userEnv := [("TZ", "/etc/shadow")] } "TZ" == none
#guard get { base with userEnv := [("TZ", ":/usr/share/zoneinfo/UTC")] } "TZ" == some ":/usr/share/zoneinfo/UTC"
#guard get { base with userEnv := [("TZ", "Europe/../../etc/x")] } "TZ" == none
#guard get { base with userEnv := [("TZ", "../x")] } "TZ" == none
#guard tzSafe "UTC" && !tzSafe "a b" && !tzSafe "/usr/share/zoneinfoX/a"

-- A function requires a value-qualified keep; "()x" is not a function prefix.
#guard get { base with
    settings := { envKeep := ["BASH_FUNC*", "F"] }
    userEnv := [("BASH_FUNC_x%%", "() { id; }"), ("F", "()x")] } "F" == some "()x"
#guard get { base with settings := { envKeep := ["BASH_FUNC*"] } } "BASH_FUNC_x%%" == none
#guard get { base with settings := { envKeep := ["BASH_FUNC*=()*"] } } "BASH_FUNC_x%%" ==
  some "() { id; }"
#guard get { base with settings := { envKeep := ["BASH_FUNC*=*"] } } "BASH_FUNC_x%%" == none
#guard get { base with settings := { envKeep := ["BASH_FUNC*", "BASH_FUNC*=()*"] } }
  "BASH_FUNC_x%%" == none

-- duplicate user entries: the last one wins, no duplicate keys
#guard get { base with userEnv := [("TERM", "a"), ("TERM", "b")] } "TERM" == some "b"
#guard ((run { base with userEnv := [("TERM", "a"), ("TERM", "b")] }).getD []).filter
  (·.1 == "TERM") == [("TERM", "b")]

-- no PATH from the user: sudo's default
#guard get { base with userEnv := [] } "PATH" == some stdPath

/-! ### -i (login shell) -/
def login : EnvInput := { base with loginShell := true }
#guard get login "PATH" == some "/home/alice/bin:/usr/bin"
#guard get login "SHELL" == some "/bin/bash"
#guard get login "HOME" == some "/root"
#guard get { login with settings := { envKeep := ["HOME", "LOGNAME"] } } "HOME" == some "/root"
#guard get { login with settings := { envKeep := ["LOGNAME"] } } "LOGNAME" == some "root"
#guard get { login with settings := { envReset := false } } "FOO" == none
#guard get { login with settings := { securePath := some "/sbin" } } "PATH" == some "/sbin"

#guard get { login with userEnv := [] } "PATH" == some stdPath
#guard get base "SUDO_HOME" == some "/home/alice"
#guard get { base with ttyName := some "/dev/pts/9" } "SUDO_TTY" == some "/dev/pts/9"
#guard get { base with setenvAllowed := true, cmdlineVars := [("SUDO_TTY", "fake")] } "SUDO_TTY" == some "fake"
#guard get { base with userEnv := [("DPKG_COLORS", "always")] } "DPKG_COLORS" == some "always"
#guard get { base with settings := { setLogname := false } } "USER" == some "alice"
#guard get { base with settings := { setLogname := false, envReset := false } } "USER" == some "alice"
#guard get { base with envFile := [("SITE", "trusted"), ("LD_PRELOAD", "/site/lib.so")] } "SITE" == some "trusted"
#guard get { base with envFile := [("LD_PRELOAD", "/site/lib.so")] } "LD_PRELOAD" == some "/site/lib.so"
#guard get { base with restrictedEnvFile := [("LD_PRELOAD", "/bad.so")] } "LD_PRELOAD" == none
#guard get { base with restrictedEnvFile := [("DISPLAY", ":4")] } "DISPLAY" == some ":0"
/-! ### -s keeps the user's SHELL; set_home applies -/
#guard get { base with shellMode := true } "SHELL" == some "/bin/zsh"
#guard get { base with shellMode := true, settings := { envKeep := ["HOME"], setHome := true } } "HOME" ==
  some "/root"
#guard get { base with settings := { envKeep := ["HOME"], setHome := true } } "HOME" == some "/home/alice"

/-! ### !env_reset (copy mode) -/
def noReset : EnvInput := { base with settings := { envReset := false } }
#guard get noReset "FOO" == some "bar"
#guard get noReset "LD_PRELOAD" == none
#guard get noReset "LD_LIBRARY_PATH" == none
#guard get noReset "IFS" == none
#guard get noReset "LC_ALL" == none
#guard get noReset "BASH_FUNC_x%%" == none
#guard get noReset "HOME" == some "/home/alice"
#guard get { noReset with setHome := true } "HOME" == some "/root"
#guard get noReset "USER" == some "root"
#guard get noReset "LOGNAME" == some "root"
#guard get noReset "SHELL" == some "/bin/zsh"
#guard get noReset "MAIL" == some "/var/mail/alice"
#guard get noReset "SUDO_USER" == some "alice"
#guard get { noReset with settings := { envReset := false, securePath := some "/s" } } "PATH" == some "/s"

/-! ### -E -/
#guard err { base with preserve := .all } == some "sorry, you are not allowed to preserve the environment"
#guard err { noReset with preserve := .all } == some "sorry, you are not allowed to preserve the environment"
def preserveAll : EnvInput := { base with preserve := .all, setenvAllowed := true }
#guard get preserveAll "FOO" == some "bar"
#guard get preserveAll "LD_PRELOAD" == none
#guard get preserveAll "HOME" == some "/home/alice"
#guard get preserveAll "USER" == some "root"

/-! ### --preserve-env=list -/
-- The CLI supplies only set variables as ordered snapshots.
#guard err { base with preserve := .vars ["FOO"], cmdlineVars := [("FOO", "bar")] } ==
  some "sorry, you are not allowed to set the following environment variables: FOO"
#guard get { base with preserve := .vars ["DISPLAY"], cmdlineVars := [("DISPLAY", ":0")] } "DISPLAY" == some ":0"
#guard get { base with preserve := .vars ["FOO"], cmdlineVars := [("FOO", "bar")], setenvAllowed := true } "FOO" == some "bar"

/-! ### VAR=value on the command line -/
#guard err { base with cmdlineVars := [("FOO", "1"), ("DISPLAY", ":1"), ("LD_PRELOAD", "x")] } ==
  some "sorry, you are not allowed to set the following environment variables: FOO, LD_PRELOAD"
#guard get { base with cmdlineVars := [("DISPLAY", ":1")] } "DISPLAY" == some ":1"
#guard get { base with cmdlineVars := [("LANG", "C")] } "LANG" == some "C"
#guard err { base with cmdlineVars := [("LANG", "../x")] } ==
  some "sorry, you are not allowed to set the following environment variables: LANG"
#guard get { base with cmdlineVars := [("FOO", "1")], setenvAllowed := true } "FOO" == some "1"
#guard get { base with cmdlineVars := [("LD_PRELOAD", "x")], setenvAllowed := true } "LD_PRELOAD" ==
  some "x"
-- Authorized assignments run after rebuilt SUDO_* and secure_path.
#guard get { base with cmdlineVars := [("SUDO_USER", "root")], setenvAllowed := true } "SUDO_USER" ==
  some "root"
#guard get { base with
    cmdlineVars := [("PATH", "/tmp")], setenvAllowed := true
    settings := { securePath := some "/sbin" } } "PATH" == some "/tmp"
#guard err { base with cmdlineVars := [("PATH", "/tmp")], settings := { securePath := some "/sbin" } } ==
  some "sorry, you are not allowed to set the following environment variables: PATH"
#guard get { base with cmdlineVars := [("PATH", "/tmp")] } "PATH" == some "/tmp"
-- SETENV bypasses function validation; without it a value-qualified keep is needed.
#guard get { base with cmdlineVars := [("F", "() { id; }")], setenvAllowed := true } "F" ==
  some "() { id; }"
#guard err { base with cmdlineVars := [("F", "() { id; }")], settings := { envKeep := ["F"] } } ==
  some "sorry, you are not allowed to set the following environment variables: F"
#guard get { base with cmdlineVars := [("F", "() { id; }")], settings := { envKeep := ["F=()*"] } } "F" == some "() { id; }"
-- copy mode: allowed unless env_delete / unsafe env_check
#guard get { noReset with cmdlineVars := [("FOO", "1")] } "FOO" == some "1"
#guard err { noReset with cmdlineVars := [("LD_PRELOAD", "x")] } ==
  some "sorry, you are not allowed to set the following environment variables: LD_PRELOAD"

/-! ### PAM environment -/
#guard get { base with pamEnv := [("PYTHONPATH", "/trusted/python")] } "PYTHONPATH" ==
  some "/trusted/python"
#guard get { base with pamEnv := [("LD_PRELOAD", "/trusted/lib.so")] } "LD_PRELOAD" ==
  some "/trusted/lib.so"
#guard get { base with pamEnv := [("SUDO_USER", "pam-user")] } "SUDO_USER" == some "pam-user"
#guard get { base with pamEnv := [("F", "() { :; }")] } "F" == some "() { :; }"
#guard get { base with pamEnv := [("LANG", "de_DE")] } "LANG" == some "en_US.UTF-8"
#guard get { base with pamEnv := [("LANG", "unsafe/value")] } "LANG" == some "unsafe/value"
#guard get { base with pamEnv := [("PATH", "/pam")] } "PATH" == some "/home/alice/bin:/usr/bin"
#guard get { base with settings := { envKeep := [], securePath := some "/secure" }, pamEnv := [("PATH", "/pam")] } "PATH" == some "/pam"
#guard get { base with setenvAllowed := true, cmdlineVars := [("SUDO_USER", "explicit")], pamEnv := [("SUDO_USER", "pam")] } "SUDO_USER" == some "pam"
#guard get { base with settings := { envKeep := ["SUDO_USER"] }, setenvAllowed := true, cmdlineVars := [("SUDO_USER", "explicit")], pamEnv := [("SUDO_USER", "pam")] } "SUDO_USER" == some "explicit"
#guard get { noReset with userEnv := [("FOO", "user")], pamEnv := [("FOO", "pam")] } "FOO" ==
  some "user"
#guard get { noReset with setenvAllowed := true, cmdlineVars := [("PYTHONPATH", "/explicit")], pamEnv := [("PYTHONPATH", "/pam")] } "PYTHONPATH" == some "/pam"
#guard get { noReset with pamEnv := [("ONLY_PAM", "added")] } "ONLY_PAM" == some "added"

/-! ### envToArray -/
#guard envToArray [("A", "1"), ("B", "x=y")] == #["A=1", "B=x=y"]

/-! ### Patterns -/
#guard patMatch "LD_*" "LD_PRELOAD" && patMatch "LD_*" "LD_" && !patMatch "LD_*" "LD"
#guard patMatch "*" "ANY" && patMatch "A" "A" && !patMatch "A" "AB" && patMatch "A*B" "AxB"
#guard patMatch "*_PROXY" "HTTP_PROXY" && patMatch "XDG_*_DIR" "XDG_CACHE_DIR"
#guard patMatch "A**B*C" "AxxByyC" && !patMatch "A*AB" "AxxAAB"
#guard patMatch "F=trusted*" "F=trusted-value" && !patMatch "*value" "F=value"
#guard (entryPattern "F=()*" "F" "() { :; }") == some true
#guard (entryPattern "F=*" "F" "() { :; }") == some false
#guard get { base with userEnv := [("HTTP_PROXY", "site")], settings := { envKeep := ["*_PROXY"] } }
  "HTTP_PROXY" == some "site"
#guard get { base with userEnv := [("XDG_CACHE_DIR", "/site")], settings := { envKeep := ["XDG_*_DIR"] } }
  "XDG_CACHE_DIR" == some "/site"
#guard get { base with userEnv := [("FOO", "trusted")], settings := { envKeep := ["FOO=trusted"] } }
  "FOO" == some "trusted"
#guard get { base with userEnv := [("FOO", "other")], settings := { envKeep := ["FOO=trusted"] } }
  "FOO" == none
#guard deleteCopy { base with settings := { envDelete := ["FOO=bad*"] } } "FOO" "bad-value"
#guard !deleteCopy { base with settings := { envDelete := ["FOO=bad*"] } } "FOO" "safe"
#guard keepReset { base with settings := { envCheck := ["FOO=ok*"], envKeep := [] } } "FOO" "okay"
#guard !keepReset { base with settings := { envCheck := ["FOO=ok*"], envKeep := [] } } "FOO" "ok/unsafe"
-- Coupling is name-only: both values survive, even when they differ.
#guard get { base with settings := { envKeep := ["LOGNAME"] }, userEnv := [("LOGNAME", "login"), ("USER", "user")] } "USER" == some "user"
#guard get { base with settings := { envKeep := ["USER"] }, userEnv := [("LOGNAME", "login"), ("USER", "user")] } "LOGNAME" == some "login"
#guard get { base with settings := { envKeep := ["USER=alice"] } } "USER" == some "root"
#guard matchesAny ["LOG*"] "USER" "different" && matchesAny ["USER"] "LOGNAME" "different"
#guard !matchesAny ["USER=alice"] "USER" "alice"
#guard deleteCopy { base with settings := { envDelete := ["USER"] } } "LOGNAME" "alice"
#guard get { base with preserve := .vars ["PATH"], setenvAllowed := true, cmdlineVars := [("PATH", "/home/alice/bin:/usr/bin")], settings := { securePath := some "/secure" } } "PATH" == some "/home/alice/bin:/usr/bin"
#guard get { base with preserve := .vars ["SUDO_USER"], setenvAllowed := true, cmdlineVars := [("SUDO_USER", "preserved")], userEnv := [("SUDO_USER", "preserved")] } "SUDO_USER" == some "preserved"
#guard get { base with preserve := .vars ["PATH"], setenvAllowed := true, cmdlineVars := [("PATH", "/preserved"), ("PATH", "/explicit")], settings := { securePath := some "/secure" } } "PATH" == some "/explicit"
#guard get { base with preserve := .vars ["PATH"], setenvAllowed := true, cmdlineVars := [("PATH", "/explicit"), ("PATH", "/preserved")], settings := { securePath := some "/secure" } } "PATH" == some "/preserved"
#guard get { base with cmdlineVars := [("SUDO_USER", "approved")], settings := { envKeep := ["SUDO_USER"] } } "SUDO_USER" == some "approved"

/-! ### Theorems instantiated -/
example (out : EnvList) (h : buildEnv base = .ok out) : (out.map Prod.fst).Nodup := buildEnv_nodup h
example (out : EnvList) (h : buildEnv { base with settings := { securePath := some "/sbin" } } = .ok out) :
    ("PATH", "/sbin") ∈ out := (buildEnv_securePath h rfl (by
      simp [BindingSafe, extraVars, pamVars, base])).1

end Tests.Env
