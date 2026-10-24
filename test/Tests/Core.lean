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
  .required { root with groups := [] }
#guard auth { ctx with settings := { ctx.settings with targetpw := true } } == .required root
#guard failure { ctx with target := bob, settings := { ctx.settings with runaspw := true } } ==
  some "sudo: runaspw requires the default runas user as target\n"
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
#guard failure { ctx with settings := { ctx.settings with intercept := true } } ==
  some "sudo: intercept mode is not supported on this system\n"
#guard execution { ctx with settings := { ctx.settings with logSubcmds := true } } == none
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

#guard failure { ctx with settings := { ctx.settings with groupPlugin := some "group_file.so" } } ==
  some "sudo: group_plugin is not supported\n"
#guard failure { editCtx with settings := { editCtx.settings with groupPlugin := some "group_file.so" } } ==
  some "sudo: group_plugin is not supported\n"
#guard failure { ctx with opts := { ctx.opts with mode := .list }, settings := { ctx.settings with groupPlugin := some "group_file.so" } } ==
  some "sudo: group_plugin is not supported\n"
#guard failure { ctx with opts := { ctx.opts with mode := .validate }, settings := { ctx.settings with groupPlugin := some "group_file.so" } } ==
  some "sudo: group_plugin is not supported\n"
#guard failure { ctx with opts := { ctx.opts with mode := .help }, settings := { ctx.settings with groupPlugin := some "group_file.so" } } == none

example (c : Context) (p : ExecPlan) (h : (decide c).action = .exec p) :
    p.uid = c.target.uid := (exec_identity c p h).1

end Tests.Core
