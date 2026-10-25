import LeanSudo.Sss
import LeanSudo.Nsswitch
import LeanSudo.Policy.List

open LeanSudo LeanSudo.Sudoers LeanSudo.Sss

#guard negation "! !\t!/bin/id" == (true, "/bin/id")
#guard negation "!! ALL" == (false, "ALL")
#guard parseOption "! authenticate" == { name := "authenticate", op := .flag false }
#guard parseOption "env_keep += \"A B\"" == { name := "env_keep", op := .add "A B" }
#guard parseOption "secure_path=/a=/b" == { name := "secure_path", op := .assign "/a=/b" }
#guard parseOption "!!authenticate" == { name := "authenticate", op := .flag true }
#guard userAtom "BOB" == .name "BOB"
#guard userAtom "*" == .name "*"
#guard userMembers ["!root", "ALL"] == [⟨false, .all⟩, ⟨true, .name "root"⟩]
#guard invokingMembers ["!bob", "ALL"] == [⟨false, .all⟩, ⟨true, .name "bob"⟩]
#guard invokingMembers ["ALL", "!bob"] == [⟨true, .name "bob"⟩, ⟨false, .all⟩]
#guard hostMembers ["!bad*", "ALL"] == [⟨false, .all⟩, ⟨true, .name "bad*"⟩]
#guard (command "!/usr/bin/id -u").toOption == some ⟨true, .command "/usr/bin/id" (.pattern "-u")⟩
#guard (command "/usr/bin/echo a,b:#=z").toOption ==
  some ⟨false, .command "/usr/bin/echo" (.pattern "a,b:#=z")⟩
#guard (command "/usr/bin/echo  x").toOption == some ⟨false, .command "/usr/bin/echo" (.pattern " x")⟩
#guard (command "/usr/bin/id \"\"").toOption == some ⟨false, .command "/usr/bin/id" .none⟩
#guard (command "ALL").toOption == some ⟨false, .all⟩

private def rule (name : String) (commands : Array String) (extra : Rule := #[]) : Rule :=
  #[("cn", #[name]), ("sudoUser", #["bob"]), ("sudoHost", #["ALL"]),
    ("sudoCommand", commands)] ++ extra

private def bob : Principal := ⟨"bob", 1001, 1001, [], "/home/bob", "/bin/sh"⟩
private def root : Principal := ⟨"root", 0, 0, [], "/root", "/bin/sh"⟩
private def request : Request := {
  user := bob, host := "host", runasUser := root, runasGroup := none, runasUserExplicit := false,
  fileIds := [("/usr/bin/id", 1, 2)],
  command := .run "/usr/bin/id" "/usr/bin/id" ["-u"] }
private def policy (rs : Array Rule) : Sudoers :=
  ((convert #[] rs).toOption.getD []).map (·.entry)
private def permitted (rs : Array Rule) : Bool :=
  match Policy.evaluate (policy rs) {} request with | .allow _ => true | .deny => false

-- SSSD delivers descending numeric sudoOrder: the first returned matching role wins.
#guard permitted #[rule "high" #["ALL"], rule "low" #["!/usr/bin/id"]]
#guard !(permitted #[rule "high" #["!/usr/bin/id"], rule "low" #["ALL"]])
-- Negative commands override positives inside a role regardless of wire ordering.
#guard !(permitted #[rule "negative" #["!/usr/bin/id", "ALL"]])
#guard !(permitted #[rule "negative" #["ALL", "!/usr/bin/id"]])
#guard !(permitted #[rule "runas" #["ALL"] #[("sudoRunAsUser", #["!root", "ALL"])]])
#guard (role #[("cn", #["empty"])]).toOption == some none
#guard permitted #[rule "nopass" #["/usr/bin/id"] #[("sudoOption", #["!authenticate"])]]
#guard ((Policy.candidates (policy #[rule "nopass" #["/usr/bin/id"]
  #[("sudoOption", #["!authenticate"])]]) {} request).head?.map (·.spec.tags.passwd)) == some (some false)
#guard Policy.listPrivileges (policy #[rule "test-role" #["/usr/bin/id"]
  #[("sudoOption", #["!authenticate", "env_keep+=FOO"])]]) {} bob "host" id true ==
  "User bob may run the following commands on host:\n\nLDAP Role: test-role\n    RunAsUsers: root\n    Options: !authenticate, env_keep+=FOO\n    Commands:\n\t/usr/bin/id\n"

-- ldap_util.c lowers root/cwd options before matching, not into post-winner Defaults.
private def rootedPolicy : Sudoers := policy #[rule "rooted" #["/usr/bin/id -u"]
  #[("sudoOption", #["runchroot=/jail", "runcwd=/work", "!authenticate"])]]
private def rootedSpecs : List CmndSpec :=
  (Policy.specsOf rootedPolicy).flatMap fun us => us.entries.flatMap (·.cmnds)
#guard rootedSpecs.map (·.options.chroot) == [some "/jail"]
#guard rootedSpecs.map (·.options.cwd) == [some (some "/work")]
#guard rootedSpecs.map (·.ldapOptions) == [["!authenticate"]]
#guard Policy.evaluate rootedPolicy {} request == .deny
private def rootedRequest : Request := { request with
  rootFacts := [("/jail", {
    command := .run "/usr/bin/id" "/usr/bin/id" ["-u"]
    argv := ["/usr/bin/id", "-u"]
    canonPaths := [("/usr/bin", "/usr/bin")]
    fileIds := [("/usr/bin/id", 9, 10)] })] }
#guard (match Policy.evaluate rootedPolicy {} rootedRequest with
  | .allow a => a.selection.map (·.root)
  | .deny => none) == some "/jail"
#guard (match Policy.evaluate rootedPolicy {} { rootedRequest with requestedChroot := some "/other" } with
  | .allow _ => false
  | .deny => true)

open LeanSudo.Nsswitch
#guard (configure "sudoers: files [NOTFOUND=return] sss").toOption ==
  some [{ name := "files", returnIfNotFound := true }, { name := "sss" }]
#guard (configure "sudoers: files files [SUCCESS=return] sss").toOption ==
  some [{ name := "files" }, { name := "sss" }]
#guard (configure "sudoers: files [SUCCESS=return] [NOTFOUND=return] sss").toOption ==
  some [{ name := "files", returnIfFound := true }, { name := "sss" }]
#guard select id false [({ name := "files", returnIfNotFound := true }, false),
  ({ name := "sss" }, true)] false == [false]
#guard select id false [({ name := "files", returnIfFound := true }, true),
  ({ name := "sss" }, false)] false == [true]
#guard select id false [({ name := "files" }, true), ({ name := "sss" }, false)] false == [true, false]
