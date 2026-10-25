import LeanSudo.CoreProofs
import LeanSudo.Sudoers.Parser

namespace Tests.Core
open LeanSudo LeanSudo.Core LeanSudo.Policy

def parsePolicy (text : String) : Sudoers.Sudoers :=
  match Sudoers.parse "sudoers" text with
  | .ok entries => entries.map (·.entry)
  | .error _ => []

def root : Principal := ⟨"root", 0, 0, [("root", 0)], "/root", "/bin/bash"⟩
def alice : Principal :=
  ⟨"alice", 1000, 1000, [("alice", 1000), ("sudo", 27), ("adm", 4)], "/home/alice", "/bin/bash"⟩
def bob : Principal := ⟨"bob", 1001, 1001, [("bob", 1001)], "/home/bob", "/bin/sh"⟩
def carol : Principal := ⟨"carol", 1002, 1002, [("carol", 1002)], "/home/carol", "/bin/sh"⟩
def policy := parsePolicy "root ALL=(ALL:ALL) ALL\n%sudo ALL=(ALL:ALL) ALL\ncarol ALL=(root) NOPASSWD: /usr/bin/id\nCmnd_Alias LIMITED = /usr/bin/true, !/usr/bin/false\ngina ALL=(root) NOPASSWD: ALL, LIMITED\n"
def idCmd : ResolvedCmd := ⟨"/usr/bin/id", "/usr/bin/id", "id", ["-u"]⟩
def ctx : Context :=
  { progname := "sudo", opts := { command := ["id", "-u"] }, invoking := alice,
    host := "box", sudoers := policy, settings := {}, target := root, targetGroup := none,
    listUser := none, command := some idCmd, userEnv := [], cwd := "/home/alice",
    userUmask := 0o022, ttyName := none, canon := id, now := 1000000000,
    tsScope := .ppid 1 1, tsRecords := [],
    fileIds := [("/usr/bin/id", 1, 1), ("/usr/bin/cat", 1, 2),
      ("/usr/bin/true", 1, 3), ("/usr/bin/false", 1, 4)], root }

def auth (c : Context) := (decide c).auth
def failure (c : Context) : Option String :=
  match (decide c).action with | .fail s _ => some s | _ => none
def printed (c : Context) : Option (String × UInt32) :=
  match (decide c).action with | .print s rc => some (s, rc) | _ => none
def execution (c : Context) : Option (Nat × Nat × List Nat × Nat) :=
  match (decide c).action with | .exec p => some (p.uid, p.gid, p.groups, p.umask) | _ => none

def cached : Context := { ctx with tsRecords := [⟨ctx.tsScope, alice.uid, ctx.now, false⟩] }
def carolCtx : Context := { ctx with invoking := carol }
def catCtx : Context :=
  { carolCtx with
    opts := { command := ["cat", "/etc/shadow"] }
    command := some ⟨"/usr/bin/cat", "/usr/bin/cat", "cat", ["/etc/shadow"]⟩ }

#guard policy.length == 5
#guard auth { ctx with invoking := root } == .none
#guard auth ctx == .required alice
#guard auth cached == .none
#guard auth { cached with opts := { ctx.opts with resetTimestamp := true } } == .required alice
#guard (decide ctx).updateTimestamp
#guard !(decide { ctx with opts := { ctx.opts with noUpdate := true } }).updateTimestamp
#guard !(decide { cached with opts := { ctx.opts with resetTimestamp := true } }).updateTimestamp
#guard auth carolCtx == .none
#guard auth catCtx == .required carol
#guard failure catCtx == some "Sorry, user carol is not allowed to execute '/usr/bin/cat /etc/shadow' as root on box.\n"
#guard !(decide catCtx).updateTimestamp
#guard auth { catCtx with settings := { catCtx.settings with authenticate := false } } == .none
#guard failure { catCtx with settings := { catCtx.settings with authenticate := false } } == failure catCtx
#guard execution { catCtx with settings := { catCtx.settings with authenticate := false } } == none
#guard failure { ctx with opts := { ctx.opts with chdir := some "/tmp" } } ==
  some "sudo: you are not permitted to use the -D option with /usr/bin/id\n"
#guard failure { carolCtx with opts := { ctx.opts with preserveEnv := .all } } ==
  some "sudo: sorry, you are not allowed to preserve the environment\n"
#guard execution { ctx with target := bob, opts := { ctx.opts with user := some "bob" } } ==
  some (1001, 1001, [1001], 0o022)
#guard execution { ctx with targetGroup := some ⟨"adm", 4⟩, opts := { ctx.opts with group := some "adm" } } ==
  some (0, 4, [0], 0o022)
#guard execution { ctx with opts := { ctx.opts with preserveGroups := true } } ==
  some (0, 0, [1000, 27, 4], 0o022)
#guard execution { ctx with settings := { ctx.settings with preserveGroups := true } } ==
  some (0, 0, [1000, 27, 4], 0o022)
#guard execution { ctx with userUmask := 0o077 } == some (0, 0, [0], 0o077)
#guard execution { ctx with userUmask := 0o077, settings := { ctx.settings with umaskOverride := true } } ==
  some (0, 0, [0], 0o022)
#guard execution { ctx with userUmask := 0o077, settings := { ctx.settings with umask := 0o777 } } ==
  some (0, 0, [0], 0o077)
#guard execution { ctx with userUmask := 0o1777, settings := { ctx.settings with umask := 0o777 } } ==
  some (0, 0, [0], 0o777)
#guard printed { carolCtx with opts := { ctx.opts with mode := .list } } ==
  some ("/usr/bin/id -u\n", 0)
#guard printed { catCtx with opts := { catCtx.opts with mode := .list } } == some ("", 1)
#guard auth { catCtx with opts := { catCtx.opts with mode := .list } } == .none
#guard failure { ctx with command := none } == some "sudo: id: command not found\n"
#guard auth { ctx with command := none } == .required alice
#guard execution { ctx with command := none } == none

def ginaCtx : Context :=
  { ctx with
    invoking := { carol with name := "gina", uid := 1003 }
    opts := { command := ["false"] }
    command := some ⟨"/usr/bin/false", "/usr/bin/false", "false", []⟩ }
#guard execution ginaCtx == none
#guard auth ginaCtx == .required ginaCtx.invoking
#guard failure ginaCtx == some "Sorry, user gina is not allowed to execute '/usr/bin/false' as root on box.\n"
#guard auth { ginaCtx with command := none, opts := { command := ["missing"] } } == .none
#guard failure { ginaCtx with command := none, opts := { command := ["missing"] } } ==
  some "sudo: missing: command not found\n"
#guard auth { ctx with target := alice } == .none
#guard auth { ctx with target := alice, targetGroup := some ⟨"adm", 4⟩, opts := { ctx.opts with group := some "adm" } } == .none
#guard auth { ctx with target := alice, targetGroup := some ⟨"root", 0⟩, opts := { ctx.opts with group := some "root" } } == .required alice
#guard failure { ctx with settings := { ctx.settings with requiretty := true } } ==
  some "sudo: sorry, you must have a tty to run sudo\n"
#guard auth { ctx with settings := { ctx.settings with requiretty := true } } == .none
#guard auth { ctx with opts := { mode := .help } } == .none
#guard auth { ctx with opts := { mode := .resetTimestamp } } == .none
#guard !(decide { ctx with opts := { mode := .removeTimestamp } }).updateTimestamp
#guard auth { ctx with settings := { ctx.settings with rootpw := true } } ==
  .required root
#guard auth { ctx with settings := { ctx.settings with targetpw := true } } == .required root
#guard auth { ctx with target := bob, settings := { ctx.settings with runaspw := true } } == .required root
#guard auth { ctx with target := bob, runasDefaultUser := some carol, settings := { ctx.settings with runaspw := true, runasDefault := "carol" } } == .required carol
#guard failure { ctx with opts := { mode := .list, otherUser := some "bob" }, listUser := some bob } ==
  some "User bob is not allowed to run sudo on box.\n"

-- Parsing a real CWD rule exercises the policy-to-plan option handoff.
def cwdCtx : Context :=
  { ctx with
    sudoers := parsePolicy "alice ALL=(root) CWD=* ALL\n"
    opts := { ctx.opts with chdir := some "/tmp" } }
#guard match (decide cwdCtx).action with | .exec p => p.cwd == some "/tmp" | _ => false
#guard match (decide { ctx with opts := { ctx.opts with login := true } }).action with
  | .exec p => p.cwd == some "/root" && p.pamService == "sudo-i" | _ => false
#guard match (decide { cwdCtx with opts := { cwdCtx.opts with login := true } }).action with
  | .exec p => p.cwd == some "/tmp" && !p.cwdOptional | _ => false
#guard match (decide { ctx with opts := { ctx.opts with login := true }, settings := { ctx.settings with runcwd := some "/tmp" } }).action with
  | .exec p => p.cwd == some "/tmp" && !p.cwdOptional | _ => false
#guard match (decide ctx).action with
  | .exec p => p.path == "/usr/bin/id" &&
    p.envInput.command == "/usr/bin/id -u" && p.argv == ["id", "-u"] | _ => false

-- Canonical parent lookup preserves the requested basename for multicall dispatch.
def aliasCtx : Context :=
  { carolCtx with
    canon := fun p => if p == "/home/carol/bin" then "/usr/bin" else p
    fileIds := ctx.fileIds ++ [("/home/carol/bin/id", 1, 1)]
    command := some ⟨"/home/carol/bin/id", "/usr/bin/id", "id", ["-u"]⟩ }
#guard match (decide aliasCtx).action with
  | .exec p => p.path == "/usr/bin/id" && p.argv == ["id", "-u"] &&
    p.envInput.command == "/home/carol/bin/id -u"
  | _ => false
#guard commandText aliasCtx == "/home/carol/bin/id -u"
#guard printed { aliasCtx with opts := { aliasCtx.opts with mode := .list } } ==
  some ("/home/carol/bin/id -u\n", 0)

-- sudoedit file and identity planning is pure; copy/edit/write safety is tested separately.
def editCtx : Context :=
  { ctx with
    opts := { mode := .edit, command := ["notes", "/etc/hosts"] }
    userEnv := [("VISUAL", "vim\t-f")]
    command := none }
#guard match (decide editCtx).action with
  | .edit p => p.files == ["/home/alice/notes", "/etc/hosts"] && p.editUid == 1000 &&
    p.fileUid == 0 && p.editors.head? == some ["vim", "-f"]
  | _ => false

def editPath (file : String) : Context :=
  { editCtx with opts := { editCtx.opts with command := [file] } }
#guard failure (editPath "/etc/../shadow") == none
#guard failure (editPath "./notes") == none
#guard failure (editPath "/etc//shadow") == none
#guard failure (editPath "//etc/shadow") == none
#guard failure (editPath "/etc/") == none
#guard failure { editPath "notes" with cwd := "/home/../root" } == none
#guard failure { editPath "notes" with cwd := "relative" } |>.isSome
#guard failure { editPath "/etc//shadow" with settings := { ctx.settings with requiretty := true } } ==
  some "sudo: sorry, you must have a tty to run sudo\n"
#guard failure (editPath "/etc/.hidden") == none
#guard failure (editPath "/etc/name..suffix") == none
#guard match (decide (editPath "./notes")).action with
  | .edit p => p.policyFiles == ["./notes"] && p.files == ["/home/alice/./notes"]
  | _ => false

-- New execution restrictions are enforced after authentication, never dropped.
#guard match (decide { ctx with settings := { ctx.settings with intercept := true } }).action with
  | .exec p => p.intercept && !p.logSubcmds
  | _ => false
#guard match (decide { ctx with settings := { ctx.settings with logSubcmds := true } }).action with
  | .exec p => !p.intercept && p.logSubcmds
  | _ => false
#guard execution { ctx with settings := { ctx.settings with logServers := ["127.0.0.1:30343"] } } |>.isSome
#guard execution { ctx with opts := { ctx.opts with host := some "remote" } } == none
#guard execution { ctx with opts := { ctx.opts with closeFrom := some 3 } } |>.isSome
#guard execution { ctx with opts := { ctx.opts with closeFrom := some 4 } } == none
#guard execution { ctx with opts := { ctx.opts with closeFrom := some 4 }, settings := { ctx.settings with closefromOverride := true } } |>.isSome
#guard execution { ctx with opts := { ctx.opts with timeout := some 2 } } == none
#guard match (decide { ctx with opts := { ctx.opts with timeout := some 2 }, settings := { ctx.settings with userCommandTimeouts := true } }).action with
  | .exec p => p.timeout == 2 | _ => false
#guard commandTimeout { ctx with opts := { ctx.opts with timeout := some 30 } } { needsAuth := false, setenv := false, cwd := none, timeout := some 5 } == 5
#guard (decide ctx).adminFlag == some "/home/alice/.sudo_as_admin_successful"
#guard (decide catCtx).adminFlag == none
#guard match (decide { ctx with settings := { ctx.settings with noexec := true } }).action with
  | .exec p => p.noexecFile == some "/usr/libexec/sudo/sudo_noexec.so" | _ => false
#guard commandText { ctx with opts := { shell := true, command := ["echo", "a b"] } } ==
  "/usr/bin/id -c echo a b"
#guard (sudoCommand { ctx with command := some { idCmd with args := [String.ofList (List.replicate 5000 'x')] } }).utf8ByteSize ==
  "/usr/bin/id ".utf8ByteSize + 4096
#guard match (decide { ctx with execFd := some 7, settings := { ctx.settings with fdexec := "always" } }).action with
  | .exec p => p.execFd == some 7 | _ => false
#guard match (decide { ctx with execFd := some 7 }).action with
  | .exec p => p.execFd == none | _ => false

#guard failure { ctx with settings := { ctx.settings with groupPlugin := some "group_file.so" } } == none
#guard failure { editCtx with settings := { editCtx.settings with groupPlugin := some "group_file.so" } } == none
#guard failure { ctx with opts := { ctx.opts with mode := .list }, settings := { ctx.settings with groupPlugin := some "group_file.so" } } == none
#guard failure { ctx with opts := { ctx.opts with mode := .validate }, settings := { ctx.settings with groupPlugin := some "group_file.so" } } == none
#guard failure { ctx with opts := { ctx.opts with mode := .help }, settings := { ctx.settings with groupPlugin := some "group_file.so" } } == none

-- Residual sudo.ws policy/message parity.
#guard failure { catCtx with longHost := "box.example.test" } ==
  some "Sorry, user carol is not allowed to execute '/usr/bin/cat /etc/shadow' as root on box.example.test.\n"
#guard failure { catCtx with settings := { catCtx.settings with cmddenialMessage := some "Ask IT" } } ==
  some "Sorry, user carol is not allowed to execute '/usr/bin/cat /etc/shadow' as root on box.\nAsk IT\n"
#guard formatAuthFailure "%d bad %% %x %" 3 == "3 bad % %x %"
#guard (authFailureLog { ctx with settings := { ctx.settings with authfailMessage := some "%d bad %%" } } 2 false).reason ==
  some "2 bad %"
#guard auth { ctx with settings := { ctx.settings with exemptGroup := some "sudo" } } == .none
#guard failure { ctx with settings := { ctx.settings with runasCheckShell := true }, validShells := [] } ==
  some "sudo: invalid shell for user root: /bin/bash\n"
#guard execution { ctx with settings := { ctx.settings with runasCheckShell := true }, validShells := ["/bin/bash"] } |>.isSome
def selfAuth : Allowed := { needsAuth := true, setenv := false, cwd := none }
#guard !policyNeedsAuth { ctx with target := alice } (.allow selfAuth)
#guard policyNeedsAuth { ctx with target := alice } (.allow { selfAuth with role := some "role" })
#guard policyNeedsAuth { ctx with target := alice } (.allow { selfAuth with type := some "type" })
#guard policyNeedsAuth { ctx with target := alice } (.allow { selfAuth with apparmorProfile := some "profile" })
#guard policyNeedsAuth { ctx with target := alice } (.allow { selfAuth with privs := some "basic" })
#guard policyNeedsAuth { ctx with target := alice } (.allow { selfAuth with limitprivs := some "basic" })

#guard failure { ctx with targetUnknownUid := true } == some "sudo: unknown user root\n"
#guard execution { ctx with targetUnknownUid := true, settings := { ctx.settings with runasAllowUnknownId := true } } |>.isSome
#guard match (decide { ctx with invokingRealGid := some 4, settings := { ctx.settings with staySetuid := true } }).action with
  | .exec p => p.gid == 4 && p.staySetuid
  | _ => false

#guard authUser { ctx with opts := { mode := .list }, settings := { ctx.settings with rootpw := true } } == alice
#guard authUser { ctx with opts := { mode := .list }, settings := { ctx.settings with targetpw := true } } == alice
#guard authUser { ctx with opts := { mode := .list }, settings := { ctx.settings with runaspw := true } } == alice
def deniedList : Context := { ctx with invoking := bob, opts := { mode := .list }, longHost := "box.example.test" }
#guard failure deniedList == some "Sorry, user bob may not run sudo on box.\n"
#guard denialReason deniedList == "command not allowed"
#guard failure { deniedList with opts := { mode := .validate } } == some "Sorry, user bob may not run sudo on box.\n"
def deniedOther : Context :=
  { carolCtx with opts := { mode := .list, otherUser := some "bob" }, listUser := some bob }
#guard listOtherDenied deniedOther
#guard failure deniedOther == some "Sorry, user carol is not allowed to execute 'list' as bob on box.\n"
#guard (decide deniedOther).log.isSome
#guard (editPlan { editCtx with settings := { editCtx.settings with envEditor := false } } selfAuth).editors.head? ==
  some ["vim", "-f"]

def rootedSelection : CommandSelection :=
  { root := "/jail", command := .run "/usr/bin/id" "/usr/bin/id" ["-u"],
    executionPath := "/usr/bin/id", argv := ["id", "-u"], execFd := some 17 }

def rootedAllowed : Allowed :=
  { needsAuth := false, setenv := false, cwd := none, chroot := some "/jail",
    selection := some rootedSelection }

def rootedFacts : RootCommandFacts :=
  { command := .run "/usr/bin/id" "/rooted/bin/id" ["-u"], argv := ["id", "-u"],
    execFd := some 17, canonPaths := [("/usr/bin", "/rooted/bin")],
    fileIds := [("/usr/bin/id", 7, 11)] }

def rootOnlyCtx : Context :=
  { ctx with command := none, execFd := some 99, settings := { fdexec := "always" }, sudoers := parsePolicy "alice ALL=(root) CHROOT=/jail NOPASSWD: /usr/bin/id -u\n", rootFacts := [("/jail", rootedFacts)] }

#guard match (decide rootOnlyCtx).action with
  | .exec p => p.path == "/rooted/bin/id" && p.chroot == some "/jail" &&
      p.execFd == some 17 && p.argv == ["id", "-u"] && p.envInput.command == "/usr/bin/id -u"
  | _ => false
#guard execution { rootOnlyCtx with rootFacts := [("/jail", { rootedFacts with found := false })] } == none
#guard failure { rootOnlyCtx with opts := { command := ["id", "-u"], chroot := some "/jail" } } ==
  some "sudo: you are not permitted to use the -R option with /usr/bin/id\n"

#guard resolvedFor { ctx with command := none } rootedAllowed == some idCmd
#guard descriptorFor { ctx with execFd := some 99 } rootedAllowed == some 17
#guard descriptorFor { ctx with execFd := some 99 }
  { rootedAllowed with selection := some { rootedSelection with execFd := none } } == none
#guard resolvedFor ctx
  { rootedAllowed with selection := some { rootedSelection with found := false } } == none
#guard resolvedFor ctx
  { rootedAllowed with selection := some { rootedSelection with argv := [] } } == none
#guard selectedExecutionPath { ctx with canon := fun _ => "/host" } rootedAllowed idCmd == "/usr/bin/id"
#guard commandChroot ctx rootedAllowed == some "/jail"
#guard !chrootPermitted { ctx with opts := { chroot := some "/jail" } } rootedAllowed
#guard chrootPermitted { ctx with opts := { chroot := some "/jail" } }
  { rootedAllowed with chroot := some "*" }
#guard commandChroot ctx
  { rootedAllowed with selection := some { rootedSelection with root := "*" } } == none
#guard commandChroot ctx
  { rootedAllowed with selection := some { rootedSelection with root := "~missing" } } == none
#guard enforcementError ctx
  { rootedAllowed with selection := some { rootedSelection with root := "~missing" } } ==
  some "invalid chroot directory: ~missing"
#guard match allowedAction { ctx with command := none }
    { rootedAllowed with selection := some { rootedSelection with found := false, refusal := some "id: command resolves outside the chroot directory" } } with
  | .fail message _ => message == "sudo: id: command resolves outside the chroot directory\n"
  | _ => false
#guard commandChroot { ctx with opts := { mode := .edit } } rootedAllowed == none
#guard !chrootPermitted { ctx with opts := { mode := .edit, chroot := some "/jail" } }
  { rootedAllowed with chroot := some "*" }
#guard commandChroot { ctx with opts := { mode := .edit }, settings := { runchroot := some "/editor-root" } }
  rootedAllowed == some "/editor-root"
#guard failure { ctx with commandSetid := true, settings := { intercept := true, interceptAllowSetid := false } } ==
  some "sudo: setid commands are not permitted in intercept mode\n"
#guard !commandSetidFor { ctx with commandSetid := true } rootedAllowed
#guard commandSetidFor ctx
  { rootedAllowed with selection := some { rootedSelection with setid := true } }
#guard commandChroot { ctx with target := carol, policyTarget := some bob }
  { rootedAllowed with selection := some { rootedSelection with root := "~" } } == some "/home/bob"
#guard commandChroot { ctx with target := carol, policyTarget := some bob, opts := { mode := .edit }, settings := { runchroot := some "~" } }
  rootedAllowed == some "/home/carol"

example (c : Context) (p : ExecPlan) (h : (decide c).action = .exec p) :
    p.uid = c.target.uid := (exec_identity c p h).1

end Tests.Core
