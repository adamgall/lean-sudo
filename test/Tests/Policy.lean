import LeanSudo.Sudoers.Parser
import LeanSudo.Policy.Eval
import LeanSudo.Policy.Defaults
import LeanSudo.Policy.List
import LeanSudo.Policy.Proofs

/-! Compile-time tests for the policy engine (ASTs built directly). -/

namespace Tests.Policy
open LeanSudo LeanSudo.Sudoers LeanSudo.Policy

/-! ## Fixtures -/

def root : Principal := ⟨"root", 0, 0, [("root", 0)], "/root", "/bin/bash"⟩
def alice : Principal :=
  ⟨"alice", 1000, 1000, [("alice", 1000), ("sudo", 27), ("adm", 4)], "/home/alice", "/bin/bash"⟩
def bob : Principal := ⟨"bob", 1001, 1001, [("bob", 1001), ("wheel", 10)], "/home/bob", "/bin/sh"⟩
def carol : Principal := ⟨"carol", 1002, 1002, [("carol", 1002)], "/home/carol", "/bin/sh"⟩

def wheelG : GroupInfo := ⟨"wheel", 10⟩
def rootG : GroupInfo := ⟨"root", 0⟩
def aliceG : GroupInfo := ⟨"alice", 1000⟩
def admG : GroupInfo := ⟨"adm", 4⟩

def pos {α : Type} (a : α) : Member α := ⟨false, a⟩
def neg {α : Type} (a : α) : Member α := ⟨true, a⟩

def spec (runas : Option RunasSpec) (c : Member CmndAtom) (tags : Tags := {})
    (opts : CmndOptions := {}) : CmndSpec :=
  { runas, options := opts, tags, cmnd := c }

def rule (users : List (Member UserAtom)) (hosts : List (Member HostAtom)) (cmnds : List CmndSpec) :
    Entry :=
  .userSpec ⟨users, [⟨hosts, cmnds⟩]⟩

def allAll : Option RunasSpec := some ⟨some [pos .all], some [pos .all]⟩
def asRoot : Option RunasSpec := some ⟨some [pos (.name "root")], none⟩
def cmd (p : String) (a : CmndArgs := .any) : CmndAtom := .command p a
def nopw : Tags := { passwd := some false }

def req (u : Principal) (c : Command) (target : Principal := root) (g : Option GroupInfo := none)
    (host : String := "box") (canon : String → String := id) : Request :=
  { user := u, host, runasUser := target, runasGroup := g, runasUserExplicit := false,
    command := c, canon
    fileIds := match c with
      | .run p _ _ => [(p, 1, 1), ("/bin/ls", 1, 1), ("/usr/bin/ls", 1, 1)]
      | _ => []
    globPaths := [("/opt/tools/*", ["/opt/tools/x"])] }

def run (p : String) (args : List String := []) : Command := .run p p args

def st : Settings := {}

def allowAuth : Judgement := .allow { needsAuth := true, setenv := false, cwd := none }
def allowNoAuth : Judgement := .allow { needsAuth := false, setenv := false, cwd := none }
def isAllow : Judgement → Bool
  | .allow _ => true
  | .deny => false
def needsAuth : Judgement → Option Bool
  | .allow a => some a.needsAuth
  | .deny => none

/-- `validate` result as a string (`Except` has no `BEq`). -/
def vres (s : Sudoers) : String :=
  match validate s with
  | .ok _ => "ok"
  | .error e => e

/-! ## Ubuntu default policy -/

def ubuntu : Sudoers := [
  .defaults .global [⟨"env_reset", .flag true⟩, ⟨"mail_badpass", .flag true⟩,
    ⟨"secure_path", .assign "/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/snap/bin"⟩,
    ⟨"use_pty", .flag true⟩],
  rule [pos (.name "root")] [pos .all] [spec allAll (pos .all)],
  rule [pos (.group "admin")] [pos .all] [spec (some ⟨some [pos .all], none⟩) (pos .all)],
  rule [pos (.group "sudo")] [pos .all] [spec allAll (pos .all)],
  .includeDir "/etc/sudoers.d"]

#guard vres ubuntu == "ok"
-- alice in %sudo: allowed with authentication; ALL implies SETENV
#guard evaluate ubuntu st (req alice (run "/usr/bin/id")) == .allow { needsAuth := true, setenv := true, cwd := none }
#guard evaluate ubuntu st (req alice (run "/usr/bin/id") (target := bob)) == .allow { needsAuth := true, setenv := true, cwd := none }
#guard evaluate ubuntu st (req alice (run "/usr/bin/id") (g := some wheelG)) == .allow { needsAuth := true, setenv := true, cwd := none }
#guard evaluate ubuntu st (req alice (.sudoedit ["/etc/hosts"])) == .allow { needsAuth := true, setenv := true, cwd := none }
#guard evaluate ubuntu st (req root (run "/bin/sh")) == .allow { needsAuth := true, setenv := true, cwd := none }
#guard evaluate ubuntu st (req bob (run "/usr/bin/id")) == .deny
#guard evaluate ubuntu { st with authenticate := false } (req alice (run "/usr/bin/id")) ==
  .allow { needsAuth := false, setenv := true, cwd := none }
#guard isAllow (evaluate ubuntu st (req alice .list))
#guard isAllow (evaluate ubuntu st (req alice .validate))
#guard evaluate ubuntu st (req bob .list) == .deny
#guard evaluate ubuntu st (req bob .validate) == .deny
#guard evaluate [] st (req root (run "/bin/ls")) == .deny

/-! ## NOPASSWD, SETENV, CWD -/

def nopasswdPol : Sudoers := [
  rule [pos (.name "bob")] [pos .all] [
    spec asRoot (pos (cmd "/usr/bin/ls")) nopw,
    spec asRoot (pos (cmd "/usr/bin/cat")) nopw,
    spec asRoot (pos (cmd "/usr/bin/vim")) { passwd := some true, setenv := some true },
    spec asRoot (pos (cmd "/usr/bin/env")) {} { cwd := some (some "/tmp") }]]

#guard evaluate nopasswdPol st (req bob (run "/usr/bin/ls")) == allowNoAuth
#guard evaluate nopasswdPol st (req bob (run "/usr/bin/vim")) == .allow { needsAuth := true, setenv := true, cwd := none }
#guard evaluate nopasswdPol st (req bob (run "/usr/bin/env")) == .allow { needsAuth := true, setenv := false, cwd := some (some "/tmp") }
#guard evaluate nopasswdPol { st with setenv := true } (req bob (run "/usr/bin/env")) ==
  .allow { needsAuth := true, setenv := true, cwd := some (some "/tmp") }
#guard evaluate nopasswdPol st (req bob (run "/usr/bin/rm")) == .deny
#guard evaluate nopasswdPol st (req bob (run "/usr/bin/ls") (target := alice)) == .deny

/-! ## Negation and last match -/

def negPol : Sudoers := [
  rule [pos (.name "alice")] [pos .all] [spec allAll (pos .all), spec allAll (neg (cmd "/usr/bin/su"))],
  rule [pos .all, neg (.name "carol")] [pos .all] [spec allAll (neg (cmd "/usr/bin/passwd"))],
  rule [pos (.name "alice")] [pos .all] [spec allAll (pos (cmd "/usr/bin/passwd" (.pattern "alice")))]]

#guard evaluate negPol st (req alice (run "/usr/bin/su")) == .deny
#guard isAllow (evaluate negPol st (req alice (run "/usr/bin/ls")))
#guard evaluate negPol st (req alice (run "/usr/bin/passwd")) == .deny
#guard isAllow (evaluate negPol st (req alice (run "/usr/bin/passwd" ["alice"])))
-- the second rule's user list excludes carol, so it gives nothing to carol either way
#guard evaluate negPol st (req carol (run "/usr/bin/passwd")) == .deny

-- the theorem in action: appending `alice ALL=(ALL:ALL) !ALL` denies everything
example : evaluate (ubuntu ++ [denyAllRule "alice"]) st (req alice (run "/usr/bin/id")) = .deny :=
  evaluate_append_deny_all ubuntu st (req alice (run "/usr/bin/id")) rfl
#guard isAllow (evaluate ubuntu st (req alice (run "/usr/bin/id")))

/-! ## Aliases -/

def aliasPol : Sudoers := [
  .userAlias "ADMINS" [pos (.name "alice"), pos (.alias "OPS")],
  .userAlias "OPS" [pos (.group "wheel"), neg (.name "carol")],
  .hostAlias "SERVERS" [pos (.name "web*"), pos (.name "DB1")],
  .cmndAlias "SHELLS" [pos (cmd "/bin/sh"), pos (cmd "/bin/bash")],
  .runasAlias "DBA" [pos (.name "postgres"), pos (.name "bob")],
  rule [pos (.alias "ADMINS")] [pos (.alias "SERVERS")]
    [spec allAll (pos .all), spec allAll (neg (.alias "SHELLS"))],
  rule [pos (.name "carol")] [pos .all] [spec (some ⟨some [pos (.alias "DBA")], none⟩) (pos (cmd "/usr/bin/psql"))]]

#guard vres aliasPol == "ok"
#guard isAllow (evaluate aliasPol st (req alice (run "/usr/bin/id") (host := "web01")))
#guard isAllow (evaluate aliasPol st (req bob (run "/usr/bin/id") (host := "db1")))
#guard evaluate aliasPol st (req alice (run "/usr/bin/id") (host := "mail")) == .deny
#guard evaluate aliasPol st (req alice (run "/bin/sh") (host := "web01")) == .deny
#guard evaluate aliasPol st (req carol (run "/usr/bin/id") (host := "web01")) == .deny
#guard isAllow (evaluate aliasPol st (req carol (run "/usr/bin/psql") (target := bob)))
#guard evaluate aliasPol st (req carol (run "/usr/bin/psql") (target := root)) == .deny

-- static checks
#guard vres [rule [pos (.alias "NOPE")] [pos .all] [spec none (pos .all)]] ==
  "User_Alias \"NOPE\" referenced but not defined"
#guard vres [.cmndAlias "A" [pos .all], .cmndAlias "A" [pos .all]] ==
  "duplicate Cmnd_Alias \"A\""
#guard vres [.userAlias "A" [pos (.alias "B")], .userAlias "B" [pos (.alias "A")]] ==
  "cycle in User_Alias \"A\""
#guard vres [.hostAlias "A" [pos (.alias "A")]] == "cycle in Host_Alias \"A\""
#guard vres [.defaults (.runas [pos (.alias "X")]) []] ==
  "Runas_Alias \"X\" referenced but not defined"
-- a User_Alias does not satisfy a Runas_Alias reference
#guard vres [.userAlias "X" [pos .all],
  rule [pos .all] [pos .all] [spec (some ⟨some [pos (.alias "X")], none⟩) (pos .all)]] ==
  "Runas_Alias \"X\" referenced but not defined"

/-! ## Hosts -/

def hostPol : Sudoers := [rule [pos .all] [pos (.name "Box"), neg (.name "box")] [spec none (pos .all)],
  rule [pos .all] [pos (.name "srv-[0-9]")] [spec none (pos .all)]]
#guard evaluate hostPol st (req bob (run "/bin/ls")) == .deny
#guard isAllow (evaluate hostPol st (req bob (run "/bin/ls") (host := "SRV-3")))
#guard evaluate hostPol st (req bob (run "/bin/ls") (host := "srv-x")) == .deny

/-! ## Run-as -/

def runasPol : Sudoers := [
  rule [pos (.name "alice")] [pos .all] [spec none (pos (cmd "/bin/a"))],
  rule [pos (.name "alice")] [pos .all] [spec asRoot (pos (cmd "/bin/b"))],
  rule [pos (.name "alice")] [pos .all] [spec (some ⟨none, some [pos (.name "wheel")]⟩) (pos (cmd "/bin/c"))],
  rule [pos (.name "alice")] [pos .all]
    [spec (some ⟨some [pos (.name "root")], some [pos (.name "wheel")]⟩) (pos (cmd "/bin/d"))],
  rule [pos (.name "alice")] [pos .all] [spec (some ⟨some [pos .all, neg (.name "root")], none⟩) (pos (cmd "/bin/e"))],
  rule [pos (.name "alice")] [pos .all] [spec (some ⟨some [pos (.group "wheel"), pos (.id 0)], some [pos (.id 4)]⟩) (pos (cmd "/bin/f"))]]

-- (a) no run-as spec: runas_default, with primary/supplementary group fallback
#guard isAllow (evaluate runasPol st (req alice (run "/bin/a")))
#guard evaluate runasPol st (req alice (run "/bin/a") (target := bob)) == .deny
#guard isAllow (evaluate runasPol { st with runasDefault := "bob" } (req alice (run "/bin/a") (target := bob)))
#guard isAllow (evaluate runasPol { st with runasDefault := "#1001" } (req alice (run "/bin/a") (target := bob)))
#guard isAllow (evaluate runasPol st (req alice (run "/bin/a") (g := some rootG)))
#guard evaluate runasPol st (req alice (run "/bin/a") (g := some wheelG)) == .deny
-- (b) users only
#guard isAllow (evaluate runasPol st (req alice (run "/bin/b")))
#guard evaluate runasPol st (req alice (run "/bin/b") (target := bob)) == .deny
#guard evaluate runasPol st (req alice (run "/bin/b") (g := some wheelG)) == .deny
#guard isAllow (evaluate runasPol st (req alice (run "/bin/b") (g := some rootG)))
-- Without -g, an unspecified run-as user is not rescued by being yourself.
#guard evaluate runasPol st (req alice (run "/bin/b") (target := alice)) == .deny
-- (c) groups only: target must be the invoking user (`sudo -g wheel`)
#guard isAllow (evaluate runasPol st (req alice (run "/bin/c") (target := alice) (g := some wheelG)))
#guard isAllow (evaluate runasPol st (req alice (run "/bin/c") (target := alice)))
#guard isAllow (evaluate runasPol st (req alice (run "/bin/c") (target := alice) (g := some admG)))
#guard evaluate runasPol st
  { (req alice (run "/bin/c") (target := root) (g := some wheelG)) with runasUserExplicit := true } == .deny
-- users and groups
#guard isAllow (evaluate runasPol st (req alice (run "/bin/d") (g := some wheelG)))
#guard isAllow (evaluate runasPol st (req alice (run "/bin/d") (target := alice) (g := some wheelG)))
#guard evaluate runasPol st (req alice (run "/bin/d") (target := bob) (g := some wheelG)) == .deny
#guard evaluate runasPol st (req alice (run "/bin/d") (g := some admG)) == .deny
-- negated run-as user
#guard isAllow (evaluate runasPol st (req alice (run "/bin/e") (target := bob)))
#guard evaluate runasPol st (req alice (run "/bin/e")) == .deny
-- %group / #uid in run-as users, #gid in run-as groups
#guard isAllow (evaluate runasPol st (req alice (run "/bin/f") (target := bob) (g := some admG)))
#guard isAllow (evaluate runasPol st (req alice (run "/bin/f") (g := some admG)))
#guard evaluate runasPol st (req alice (run "/bin/f") (target := carol)) == .deny
#guard evaluate runasPol st (req alice (run "/bin/f") (target := bob) (g := some aliceG)) == .deny

def bobAsAlice : Sudoers := [
  rule [pos (.name "bob")] [pos .all]
    [spec (some ⟨some [pos (.name "alice")], none⟩) (pos (cmd "/usr/bin/id"))]]
#guard evaluate bobAsAlice st
  { (req bob (run "/usr/bin/id") bob) with runasUserExplicit := true } == .deny
#guard evaluate bobAsAlice st (req bob (run "/usr/bin/id") bob (some ⟨"bob", 1001⟩)) == .deny
#guard isAllow (evaluate bobAsAlice st (req bob (run "/usr/bin/id") alice (some admG)))

def erin : Principal := ⟨"erin", 1003, 1003, [("erin", 1003)], "/home/erin", "/bin/sh"⟩
def erinGroupOnly : Sudoers := [
  rule [pos (.name "erin")] [pos .all]
    [spec (some ⟨none, some [pos (.name "adm")]⟩) (pos (cmd "/usr/bin/id"))]]
#guard isAllow (evaluate erinGroupOnly st (req erin (run "/usr/bin/id") erin (some admG)))
#guard evaluate erinGroupOnly st
  { (req erin (run "/usr/bin/id") root (some admG)) with runasUserExplicit := true } == .deny
#guard isAllow (evaluate [rule [pos .all] [pos .all] [spec allAll (pos .all)]]
  st (req bob (run "/usr/bin/id") alice (some wheelG)))

def runasGroupAliasPol : Sudoers := [
  .runasAlias "NOTADM" [pos .all, neg (.name "adm")],
  rule [pos .all] [pos .all]
    [spec (some ⟨some [pos .all], some [pos (.alias "NOTADM")]⟩) (pos .all)]]
-- Inner DENY defeats even the matched target's supplementary-group fallback.
#guard evaluate runasGroupAliasPol st (req bob (run "/usr/bin/id") alice (some admG)) == .deny
#guard isAllow (evaluate runasGroupAliasPol st (req bob (run "/usr/bin/id") alice (some wheelG)))
-- sudo applies fallback within aliases too, before an outer negation.
#guard evaluate [
    .runasAlias "OTHER" [pos (.name "wheel")],
    rule [pos .all] [pos .all]
      [spec (some ⟨some [pos .all], some [neg (.alias "OTHER")]⟩) (pos .all)]]
  st (req bob (run "/usr/bin/id") alice (some admG)) == .deny

/-! ## Commands: arguments, directories, globs, canonical paths, sudoedit -/

def cmdPol : Sudoers := [
  rule [pos (.name "bob")] [pos .all] [
    spec asRoot (pos (cmd "/usr/bin/whoami" .none)),
    spec asRoot (pos (cmd "/usr/bin/apt" (.pattern "update"))),
    spec asRoot (pos (cmd "/usr/bin/systemctl" (.pattern "restart *"))),
    spec asRoot (pos (cmd "/usr/local/bin/")),
    spec asRoot (pos (cmd "/opt/tools/*")),
    spec asRoot (pos (cmd "/bin/ls")),
    spec asRoot (pos (cmd "/usr/bin/id")),
    spec asRoot (pos (.sudoedit (.pattern "/etc/hosts")))]]

#guard isAllow (evaluate cmdPol st (req bob (run "/usr/bin/whoami")))
#guard evaluate cmdPol st (req bob (run "/usr/bin/whoami" ["-x"])) == .deny
#guard isAllow (evaluate cmdPol st (req bob (run "/usr/bin/apt" ["update"])))
#guard evaluate cmdPol st (req bob (run "/usr/bin/apt" ["install", "x"])) == .deny
#guard evaluate cmdPol st (req bob (run "/usr/bin/apt")) == .deny
#guard isAllow (evaluate cmdPol st (req bob (run "/usr/bin/systemctl" ["restart", "nginx"])))
#guard evaluate cmdPol st (req bob (run "/usr/bin/systemctl" ["stop", "nginx"])) == .deny
-- directory
#guard isAllow (evaluate cmdPol st (req bob (run "/usr/local/bin/foo" ["any", "args"])))
#guard evaluate cmdPol st (req bob (run "/usr/local/bin/sub/foo")) == .deny
#guard evaluate cmdPol st (req bob (run "/usr/local/foo")) == .deny
-- glob (FNM_PATHNAME)
#guard isAllow (evaluate cmdPol st (req bob (run "/opt/tools/x")))
#guard evaluate cmdPol st (req bob (run "/opt/tools/a/x")) == .deny
-- usr-merge: sudoers says /bin/ls, the user runs /usr/bin/ls
def usrMerge : String → String := fun p =>
  if p == "/bin/ls" then "/usr/bin/ls" else if p == "/bin" then "/usr/bin" else p
#guard isAllow (evaluate cmdPol st (req bob (.run "/usr/bin/ls" "/usr/bin/ls" []) (canon := usrMerge)))
#guard evaluate cmdPol st (req bob (.run "/usr/bin/ls" "/usr/bin/ls" [])) == .deny
-- multicall binaries: /usr/bin/id and /usr/bin/rm both resolve to one binary
def multicall : String → String := fun p =>
  if p == "/usr/bin/id" || p == "/usr/bin/rm" then "/usr/lib/coreutils" else p
#guard isAllow (evaluate cmdPol st (req bob (.run "/usr/bin/id" "/usr/lib/coreutils" []) (canon := multicall)))
#guard evaluate cmdPol st (req bob (.run "/usr/bin/rm" "/usr/lib/coreutils" []) (canon := multicall)) == .deny
-- directory rule through a canonical directory
def dirPol : Sudoers := [rule [pos (.name "bob")] [pos .all] [spec asRoot (pos (cmd "/bin/"))]]
#guard isAllow (evaluate dirPol st (req bob (.run "/usr/bin/ls" "/usr/bin/ls" []) (canon := usrMerge)))
#guard evaluate dirPol st (req bob (.run "/usr/sbin/ls" "/usr/sbin/ls" []) (canon := usrMerge)) == .deny
-- sudoedit
#guard isAllow (evaluate cmdPol st (req bob (.sudoedit ["/etc/hosts"])))
#guard evaluate cmdPol st (req bob (.sudoedit ["/etc/shadow"])) == .deny
#guard evaluate cmdPol st (req bob (run "sudoedit" ["/etc/hosts"])) == .deny

/-! ## `listpw` / `verifypw` -/

def pwPol : Sudoers := [
  rule [pos (.name "bob")] [pos .all] [spec asRoot (pos (cmd "/bin/a")) nopw, spec asRoot (pos (cmd "/bin/b"))],
  rule [pos (.name "carol")] [pos .all] [spec asRoot (pos (cmd "/bin/a")) nopw],
  rule [pos (.name "alice")] [pos .all] [spec asRoot (neg (cmd "/bin/a"))]]

#guard needsAuth (evaluate pwPol st (req bob .list)) == some false      -- listpw=any
#guard needsAuth (evaluate pwPol { st with listpw := .all } (req bob .list)) == some true
#guard needsAuth (evaluate pwPol { st with listpw := .all } (req carol .list)) == some false
#guard needsAuth (evaluate pwPol { st with listpw := .always } (req carol .list)) == some true
#guard needsAuth (evaluate pwPol { st with listpw := .never } (req bob .list)) == some false
#guard needsAuth (evaluate pwPol st (req bob .validate)) == some true   -- verifypw=all
#guard needsAuth (evaluate pwPol st (req carol .validate)) == some false
#guard needsAuth (evaluate pwPol { st with verifypw := .any } (req bob .validate)) == some false
-- A matching user/host entry permits listing, even when every command is denied.
#guard isAllow (evaluate pwPol st (req alice .list))

/-! ## Defaults -/

def resolveS (s : Sudoers) (u : Principal) (host : String := "box") (runas : Option Principal := none)
    (c : Option Command := none) : Option Settings :=
  (resolveDefaults s u host runas c).toOption.map (·.1)

def warnings (s : Sudoers) : List String :=
  ((resolveDefaults s alice "box" none none).toOption.map (·.2)).getD ["<error>"]

def isErr (s : Sudoers) : Bool :=
  match resolveDefaults s alice "box" none none with
  | .error _ => true
  | .ok _ => false

def g1 (n : String) (op : DefaultsOp) : Entry := .defaults .global [⟨n, op⟩]

def scopePol : Sudoers := [
  .defaults (.cmnd [pos (cmd "/usr/bin/ls")]) [⟨"passwd_tries", .assign "9"⟩],
  .defaults (.runas [pos (.name "bob")]) [⟨"passwd_tries", .assign "8"⟩],
  .defaults (.user [pos (.name "alice")]) [⟨"passwd_tries", .assign "2"⟩],
  .defaults (.host [pos (.name "box")]) [⟨"passwd_tries", .assign "4"⟩],
  g1 "passwd_tries" (.assign "5"),
  .defaults (.user [pos (.group "wheel")]) [⟨"rootpw", .flag true⟩]]

#guard (resolveS scopePol carol (host := "other")).map (·.passwdTries) == some 5
#guard (resolveS scopePol carol).map (·.passwdTries) == some 5
#guard (resolveS scopePol alice).map (·.passwdTries) == some 5
#guard (resolveS scopePol alice (runas := some bob)).map (·.passwdTries) == some 8
#guard (resolveS scopePol alice (runas := some root)).map (·.passwdTries) == some 5
#guard (resolveS scopePol alice (runas := some bob) (c := some (run "/usr/bin/ls"))).map (·.passwdTries) == some 9
#guard (resolveS scopePol bob).map (·.rootpw) == some true
#guard (resolveS scopePol alice).map (·.rootpw) == some false

-- list operations
def listPol : Sudoers := [
  g1 "env_keep" (.assign "A B"), g1 "env_keep" (.add "C  D"), g1 "env_keep" (.add "A"),
  g1 "env_keep" (.remove "B"), g1 "env_check" (.flag false), g1 "env_delete" (.add "FOO")]
#guard (resolveS listPol alice).map (·.envKeep) == some ["A", "C", "D"]
#guard (resolveS listPol alice).map (·.envCheck) == some []
#guard (resolveS listPol alice).map (·.envDelete.getLast?) == some (some "FOO")

-- typed values
#guard (resolveS [g1 "timestamp_timeout" (.assign "2.5")] alice).map (·.timestampTimeout) == some (some 150)
#guard (resolveS [g1 "timestamp_timeout" (.assign "0")] alice).map (·.timestampTimeout) == some (some 0)
#guard (resolveS [g1 "timestamp_timeout" (.assign "-1")] alice).map (·.timestampTimeout) == some none
#guard (resolveS [g1 "timestamp_timeout" (.flag false)] alice).map (·.timestampTimeout) == some (some 0)
#guard (resolveS [g1 "umask" (.assign "077")] alice).map (·.umask) == some 0o77
#guard (resolveS [g1 "umask" (.flag false)] alice).map (·.umask) == some 0o777
#guard (resolveS [g1 "listpw" (.assign "never")] alice).map (·.listpw) == some .never
#guard (resolveS [g1 "verifypw" (.flag false)] alice).map (·.verifypw) == some .never
#guard (resolveS [g1 "timestamp_type" (.assign "ppid")] alice).map (·.timestampType) == some .ppid
#guard (resolveS [g1 "tty_tickets" (.flag false)] alice).map (·.timestampType) == some .global
#guard (resolveS [g1 "secure_path" (.assign "/bin")] alice).map (·.securePath) == some (some "/bin")
#guard (resolveS [g1 "secure_path" (.assign "/bin"), g1 "secure_path" (.flag false)] alice).map (·.securePath) == some none
#guard (resolveS [g1 "syslog" (.flag false)] alice).map (·.syslog) == some none
#guard (resolveS [g1 "env_reset" (.flag false), g1 "authenticate" (.flag false)] alice).map
  (fun s => (s.envReset, s.authenticate)) == some (false, false)
#guard (resolveS [g1 "runas_default" (.assign "bob"), g1 "passprompt" (.assign "pw: ")] alice).map
  (fun s => (s.runasDefault, s.passprompt)) == some ("bob", "pw: ")

-- errors (fail-closed) and warnings
#guard isErr [g1 "passwd_tries" (.assign "abc")]
#guard isErr [g1 "umask" (.assign "0999")]
#guard isErr [g1 "timestamp_timeout" (.assign "1.2.3")]
#guard isErr [g1 "listpw" (.assign "sometimes")]
#guard isErr [g1 "env_reset" (.assign "yes")]
#guard isErr [g1 "secure_path" (.flag true)]
#guard isErr [g1 "passwd_tries" (.add "1")]
#guard isErr [g1 "syslog" (.assign "nonsense")]
#guard !isErr [g1 "noexec" (.flag true)]
#guard !isErr [g1 "env_file" (.assign "/etc/x")]
#guard !isErr [g1 "rlimit_core" (.assign "0")]
#guard !isErr [g1 "runcwd" (.assign "/")]
#guard warnings [g1 "mail_badpass" (.flag true)] == []
#guard warnings [g1 "frobnicate" (.flag true)] == ["unknown defaults entry \"frobnicate\""]
#guard warnings ubuntu == []
#guard (resolveS ubuntu alice).map (fun s => (s.usePty, s.securePath)) ==
  some (true, some "/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/snap/bin")

/-! ## `sudo -l` rendering -/

#guard listPrivileges ubuntu st alice "box" ==
  "Matching Defaults entries for alice on box:\n" ++
  "    env_reset, mail_badpass, secure_path=/usr/local/sbin\\:/usr/local/bin\\:/usr/sbin\\:/usr/bin\\:/sbin\\:/bin\\:/snap/bin, use_pty\n" ++
  "\n" ++
  "User alice may run the following commands on box:\n" ++
  "    (ALL : ALL) ALL\n"

#guard listPrivileges ubuntu st bob "box" == "User bob is not allowed to run sudo on box.\n"

def listPol2 : Sudoers := [
  .defaults (.user [pos (.name "bob")]) [⟨"env_keep", .add "LANG LC_ALL"⟩],
  .defaults (.user [pos (.name "alice")]) [⟨"rootpw", .flag true⟩],
  .defaults (.runas [pos (.name "root")]) [⟨"set_logname", .flag false⟩],
  .defaults (.cmnd [pos (cmd "/usr/bin/vi")]) [⟨"env_reset", .flag false⟩, ⟨"umask", .assign "077"⟩],
  rule [pos (.name "bob")] [pos .all] [
    spec asRoot (pos (cmd "/usr/bin/ls")) nopw,
    spec asRoot (pos (cmd "/usr/bin/cat" (.pattern "/var/log/*"))) nopw,
    spec asRoot (neg (cmd "/usr/bin/su")) {},
    spec asRoot (pos (cmd "/usr/bin/whoami" .none)) { passwd := some true },
    spec none (pos (.alias "SHELLS")),
    spec (some ⟨none, some [pos (.name "wheel")]⟩) (pos (cmd "/bin/c")),
    spec allAll (pos (.sudoedit (.pattern "/etc/hosts"))) { setenv := some true } { cwd := some none }]]

#guard listPrivileges listPol2 st bob "box" ==
  "Matching Defaults entries for bob on box:\n" ++
  "    env_keep+=\"LANG LC_ALL\"\n" ++
  "\n" ++
  "Runas and Command-specific defaults for bob:\n" ++
  "    Defaults>root !set_logname" ++
  "    Defaults!/usr/bin/vi !env_reset, umask=077\n" ++
  "\n" ++
  "User bob may run the following commands on box:\n" ++
  "    (root) NOPASSWD: /usr/bin/ls, /usr/bin/cat /var/log/*, !/usr/bin/su, PASSWD: /usr/bin/whoami \"\"\n" ++
  "    (root) SHELLS\n" ++
  "    (bob : wheel) /bin/c\n" ++
  "    (ALL : ALL) CWD=* SETENV: sudoedit /etc/hosts\n"

#guard notAllowedMessage "bob" "box" == "User bob is not allowed to run sudo on box."

/-! ## Alias DENY propagation through real sudoers syntax -/

def parsed (text : String) : Option Sudoers :=
  (LeanSudo.Sudoers.parse "alias-regression" text).toOption.map (·.map (·.entry))

def parsedEval (text : String) (r : Request) : Option Judgement :=
  (parsed text).map (fun s => evaluate s st r)

def limitedText :=
  "Cmnd_Alias LIMITED = /usr/bin/true, !/usr/bin/false\nalice ALL=(root) NOPASSWD: ALL, LIMITED\n"
#guard parsedEval limitedText (req alice (run "/usr/bin/false")) == some .deny
#guard parsedEval limitedText (req alice (run "/usr/bin/true")) == some allowNoAuth

def notbobText := "User_Alias NOTBOB = ALL, !bob\nNOTBOB ALL=(ALL) ALL\n"
#guard parsedEval notbobText (req bob (run "/usr/bin/id")) == some .deny
#guard (parsedEval notbobText (req alice (run "/usr/bin/id"))).map isAllow == some true
def notbobLastText := "User_Alias NOTBOB = ALL, !bob\nALL, NOTBOB ALL=(ALL) ALL\n"
#guard parsedEval notbobLastText (req bob (run "/usr/bin/id")) == some .deny
def notbobNegText := "User_Alias NOTBOB = ALL, !bob\nALL, !NOTBOB ALL=(ALL) ALL\n"
#guard (parsedEval notbobNegText (req bob (run "/usr/bin/id"))).map isAllow == some true
#guard parsedEval notbobNegText (req alice (run "/usr/bin/id")) == some .deny

def hostDenyText := "Host_Alias H = ALL, !thishost\nalice H=(ALL) ALL\n"
#guard parsedEval hostDenyText (req alice (run "/usr/bin/id") (host := "thishost")) == some .deny
#guard (parsedEval hostDenyText (req alice (run "/usr/bin/id") (host := "elsewhere"))).map isAllow == some true

def runasDenyText := "Runas_Alias R = ALL, !root\nalice ALL=(R) ALL\n"
#guard parsedEval runasDenyText (req alice (run "/usr/bin/id")) == some .deny
#guard (parsedEval runasDenyText (req alice (run "/usr/bin/id") (target := bob))).map isAllow == some true
def groupDenyText := "Runas_Alias R = ALL, !root\nalice ALL=(ALL:R) ALL\n"
#guard parsedEval groupDenyText (req alice (run "/usr/bin/id") (g := some rootG)) == some .deny
#guard (parsedEval groupDenyText (req alice (run "/usr/bin/id") (g := some wheelG))).map isAllow == some true

def nestedCmndText := "Cmnd_Alias A = B\nCmnd_Alias B = ALL, !/usr/bin/x\nalice ALL=(ALL) ALL, A\n"
#guard parsedEval nestedCmndText (req alice (run "/usr/bin/x")) == some .deny
#guard (parsedEval nestedCmndText (req alice (run "/usr/bin/y"))).map isAllow == some true
def nestedUserText := "User_Alias A = B\nUser_Alias B = ALL, !bob\nALL, A ALL=(ALL) ALL\n"
#guard parsedEval nestedUserText (req bob (run "/usr/bin/id")) == some .deny
#guard (parsedEval nestedUserText (req alice (run "/usr/bin/id"))).map isAllow == some true

def scopedText :=
  "User_Alias NOTBOB = ALL, !bob\nDefaults:NOTBOB !authenticate\n"
def parsedAuth (text : String) (u : Principal) : Option Bool := do
  let s ← parsed text
  let result ← (resolveDefaults s u "box" none none).toOption
  pure result.1.authenticate
#guard parsedAuth scopedText bob == some true
#guard parsedAuth scopedText alice == some false

/-! sudoedit arguments are matched with `FNM_PATHNAME` (as sudo does): `*` must not
match `/`, so `sudoedit /etc/app/*` does not cover `/etc/app/../shadow`. -/
def editGlob : Sudoers :=
  [rule [pos (.name "bob")] [pos .all] [spec asRoot (pos (.sudoedit (.pattern "/etc/app/*")))]]
#guard isAllow (evaluate editGlob st (req bob (.sudoedit ["/etc/app/conf"])))
#guard !isAllow (evaluate editGlob st (req bob (.sudoedit ["/etc/app/../shadow"])))
#guard !isAllow (evaluate editGlob st (req bob (.sudoedit ["/etc/app/sub/conf"])))
-- ordinary command arguments keep sudo's non-pathname matching
def argGlob : Sudoers :=
  [rule [pos (.name "bob")] [pos .all] [spec asRoot (pos (cmd "/usr/bin/cat" (.pattern "/var/log/*")))]]
#guard isAllow (evaluate argGlob st (req bob (run "/usr/bin/cat" ["/var/log/a/b"])))

/-! ## sudo 1.9.17 matching regressions -/

def selfText := "bob ALL=() NOPASSWD: /usr/bin/id\n"
#guard parsedEval selfText (req bob (run "/usr/bin/id")) == some .deny
#guard parsedEval selfText (req bob (run "/usr/bin/id") bob) == some allowNoAuth
#guard parsedEval "bob ALL=(:) NOPASSWD: /usr/bin/id\n" (req bob (run "/usr/bin/id")) == some .deny
#guard parsedEval "bob ALL, !box.example.com = NOPASSWD: ALL\n"
  { (req bob (run "/usr/bin/id")) with lhost := "box.example.com" } == some .deny
#guard parsedEval "ALL, !BoB ALL=NOPASSWD: ALL\n" (req bob (run "/usr/bin/id")) == some .deny
#guard parsedEval "bob ALL=(ALL,!RoOt) NOPASSWD: ALL\n" (req bob (run "/usr/bin/id")) == some .deny
#guard !userBase bob {} none (.nonunixGroup "wheel")
#guard userBase bob {} none (.group "WhEeL")
#guard !userBase bob { caseInsensitiveGroup := false } none (.group "WhEeL")
#guard !userBase bob { caseInsensitiveUser := false } none (.name "BoB")
#guard parsedEval "\\x62ob ALL=NOPASSWD: /usr/bin/id\n" (req bob (run "/usr/bin/id")) == some allowNoAuth

def pathFacts : Request :=
  { (req bob (.run "/bin/id" "/usr/bin/id" []) (canon := usrMerge)) with
    fileIds := [("/bin/id", 1, 2), ("/usr/bin/id", 1, 2), ("/home/bob/id", 1, 2)]
    globPaths := [("/usr/bin/i*", ["/usr/bin/id"])] }
#guard pathMatches usrMerge "/usr/bin/id" "/bin/id" "/usr/bin/id" (some pathFacts)
#guard !pathMatches usrMerge "/usr/bin/id" "/home/bob/id" "/usr/bin/id" (some pathFacts)
#guard pathMatches usrMerge "/usr/bin/i*" "/bin/id" "/usr/bin/id" (some pathFacts)
#guard pathMatches usrMerge "/usr/bin/i*" "/bin/id" "/usr/bin/id" (some { pathFacts with fastGlob := true })
#guard !pathMatches usrMerge "/usr/bin/id" "/bin/id" "/usr/bin/id"
  (some { pathFacts with fileIds := [("/bin/id", 1, 3), ("/usr/bin/id", 1, 2)] })
#guard parsedEval "bob ALL=NOPASSWD: ALL, !/usr/bin/i*\n" pathFacts == some .deny

def oracleFacts : Request :=
  { (req bob (run "/usr/bin/id" ["-u"])) with
    lhost := "box.example.com", now := 100
    interfaces := [(.v4 [192, 0, 2, 10], .v4 [255, 255, 255, 0])]
    netgroups := [("ops", some "bob", none, true),
      ("machines", none, some "box.example.com", true),
      ("tuple", some "bob", some "box.example.com", true)]
    regexMatches := [("^/usr/bin/i[d]$", "/usr/bin/id", true), ("^-u$", "-u", true)]
    digests := [{ algo := .sha256, bytes := [1, 2, 3] }] }
#guard userBase bob {} (some oracleFacts) (.netgroup "ops")
#guard !userBase bob { useNetgroups := false } (some oracleFacts) (.netgroup "ops")
#guard userBase bob { netgroupTuple := true } (some oracleFacts) (.netgroup "tuple")
#guard hostBase "box" {} (some oracleFacts) (.netgroup "machines")
#guard hostBase "box" {} (some oracleFacts) (.network (.v4 [192, 0, 2, 0]) (.v4 [255, 255, 255, 0]))
#guard !hostBase "box" {} (some oracleFacts) (.network (.v4 [192, 0, 3, 0]) (.v4 [255, 255, 255, 0]))
#guard hostBase "box" {} (some oracleFacts) (.network (.v4 [192, 0, 2, 0]) (.v4 []))
#guard hostBase "box" {} (some oracleFacts) (.network (.v4 [192, 0, 2, 10]) (.v4 []))
#guard !hostBase "box" {} (some oracleFacts) (.network (.v4 [192, 0, 2, 0]) (.v4 [255, 255, 255, 255]))
#guard !hostBase "box" {} (some oracleFacts) (.network (.v4 [192, 0, 2, 0]) (.v4 [0]))
#guard cmndBase id oracleFacts.command (.commandRegex "^/usr/bin/i[d]$" (.regex "^-u$")) (some oracleFacts)
#guard !argsMatch false (.regex "^-x$") ["-u"] (some oracleFacts)
#guard cmndBase id oracleFacts.command (.digest [{ algo := .sha256, bytes := [1, 2, 3], spelling := "AQID" }] (.command "/usr/bin/id" .any)) (some oracleFacts)
#guard !cmndBase id oracleFacts.command (.digest [{ algo := .sha256, bytes := [3, 2, 1] }] (.command "/usr/bin/id" .any)) (some oracleFacts)
#guard !specApplies {} 1 {} oracleFacts (spec asRoot (pos .all) {} { notBefore := some 101 })
#guard !specApplies {} 1 {} oracleFacts (spec asRoot (pos .all) {} { notAfter := some 99 })
#guard specApplies {} 1 {} oracleFacts (spec asRoot (pos .all) {} { notBefore := some 100, notAfter := some 100 })
#guard specApplies {} 1 {} { oracleFacts with command := .list }
  (spec asRoot (neg .all) {} { notBefore := some 101, notAfter := some 99 })
#guard !specApplies {} 1 {} { oracleFacts with command := .checkList }
  (spec asRoot (pos .list) {} { notBefore := some 101 })
#guard runasGroupOk {} 1 (req bob (run "/usr/bin/id") root (some wheelG)) none { preserveGroups := true }
#guard !runasGroupOk {} 1 (req bob (run "/usr/bin/id") root (some wheelG)) none {}
#guard cmndBase id .checkList .list none
#guard !cmndBase id (run "/usr/bin/list") .list none
#guard canListOther [rule [pos (.name "bob")] [pos .all] [spec asRoot (pos .all)]]
  {} (req bob .list) alice root
#guard !canListOther [rule [pos (.name "bob")] [pos .all] [spec asRoot (pos .list)]]
  {} (req bob .list) alice root
#guard canListOther [rule [pos (.name "bob")] [pos .all]
  [spec (some ⟨some [pos (.name "alice")], none⟩) (pos .list)]]
  {} (req bob .list) alice root

def digestAliases : Aliases :=
  { cmnd := [("D", [pos (.digest [{ algo := .sha256, bytes := [1, 2, 3] }] (cmd "/usr/bin/id"))]),
    ("N", [pos (.alias "D")])] }
#guard cmndUsesDigest digestAliases oracleFacts 3 (.alias "N")
#guard !cmndUsesDigest { cmnd := [("D", [pos (.digest [{ algo := .sha256, bytes := [1, 2, 3] }] (cmd "/usr/bin/id")), pos .all])] }
  oracleFacts 2 (.alias "D")
#guard (allowedOf {} (candidateOf digestAliases 3 oracleFacts (spec asRoot (pos (.alias "N"))))).usesDigest
#guard !(allowedOf {} (candidateOf digestAliases 3 oracleFacts (spec asRoot (pos .all)))).usesDigest

#guard isRunasDefault { runasDefault := "ROOT" } root
#guard !isRunasDefault { runasDefault := "ROOT", caseInsensitiveUser := false } root
#guard runasGroupOk {} 1 (req bob (run "/usr/bin/id") root (some rootG)) none { preserveGroups := true }
#guard hostBase "box" {} (some { oracleFacts with netgroups := [("short", none, some "box", true)] }) (.netgroup "short")
#guard inTimeWindow 100 (spec asRoot (pos .all) {} { notBefore := some 200, notBeforeLocal := true }) 100
#guard !inTimeWindow 100 (spec asRoot (pos .all) {} { notBefore := some 200, notBeforeLocal := true }) 99
#guard inTimeWindow 100 (spec asRoot (pos .all) {} { notAfter := some 50, notAfterLocal := true }) (-50)
#guard !inTimeWindow 100 (spec asRoot (pos .all) {} { notAfter := some 50, notAfterLocal := true }) 0
#guard commandImpliesSetenv (.digest [{ algo := .sha256, bytes := [1] }] .all)
#guard cmndBase id .checkList (.digest [{ algo := .sha256, bytes := [1] }] .list) none
#guard cmndBase id (.sudoedit ["/etc/hosts"])
  (.digest [{ algo := .sha256, bytes := [1] }] (.sudoedit (.pattern "/etc/hosts"))) none
#guard !cmndUsesDigest {} oracleFacts 1 (.digest [{ algo := .sha256, bytes := [1] }] .list)

end Tests.Policy
