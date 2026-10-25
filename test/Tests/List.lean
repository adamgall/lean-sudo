import LeanSudo.Policy.List
import LeanSudo.Sudoers.Parser

namespace Tests.Listing
open LeanSudo LeanSudo.Sudoers LeanSudo.Policy

def alice : Principal := ⟨"alice", 1000, 1000, [], "/home/alice", "/bin/bash"⟩
def policy := "Cmnd_Alias SHELLS = /bin/sh, !/bin/bash\nRunas_Alias ADMINS = root, !daemon\nalice ALL = (ADMINS : root) SETENV: NOPASSWD: ALL, !SHELLS, (root) /bin/true, (root) /bin/false\n"
def render (text : String) (verbose : Bool := false) (facts : Option Request := none) : Option String := do
  let located ← (parse "/etc/sudoers.d/test" text).toOption
  pure (listPrivileges (located.map (·.entry)) {} alice "box" id verbose located facts)

#guard renderGeneralizedTime 0 == "19700101000000Z"
#guard renderGeneralizedTime 951782400 == "20000229000000Z"
#guard renderGeneralizedTime 4107542400 == "21000301000000Z"
#guard renderGeneralizedTime 1704067200 == "20240101000000Z"
#guard render policy == some (
  "User alice may run the following commands on box:\n" ++
  "    (root, !daemon : root) SETENV: NOPASSWD: ALL, !/bin/sh, /bin/bash\n" ++
  "    (root) SETENV: NOPASSWD: /bin/true\n" ++
  "    (root) SETENV: NOPASSWD: /bin/false\n")
#guard render "alice ALL = (:root) NOPASSWD: /bin/true\n" == some (
  "User alice may run the following commands on box:\n    (alice : root) NOPASSWD: /bin/true\n")
#guard render "alice ALL = () NOPASSWD: /bin/true\n" == some (
  "User alice may run the following commands on box:\n    (alice) NOPASSWD: /bin/true\n")
#guard render "alice ALL = (root) NOPASSWD: /bin/true, /bin/false\n" true == some (
  "User alice may run the following commands on box:\n\n" ++
  "Sudoers entry: /etc/sudoers.d/test\n    RunAsUsers: root\n" ++
  "    Options: !authenticate\n    Commands:\n\t/bin/true\n\t/bin/false\n")
#guard render "alice ALL = (root) NOEXEC: SETENV: INTERCEPT: NOPASSWD: LOG_OUTPUT: FOLLOW: /bin/true\n" == some (
  "User alice may run the following commands on box:\n" ++
  "    (root) SETENV: INTERCEPT: NOEXEC: NOPASSWD: LOG_OUTPUT: FOLLOW: /bin/true\n")

#guard wrapListing "one two three four five six seven eight\n" 30 8 ==
  "one two three four five six\n        seven eight\n"
#guard wrapListing "012345678901234567890123456789012345 rest\n" 30 8 ==
  "012345678901234567890123456789012345\n        rest\n"
#guard wrapListing "one two three four\n" 0 8 == "one two three four\n"

def root : Principal := ⟨"root", 0, 0, [], "/root", "/bin/sh"⟩
def timeFacts : Request :=
  { user := alice, host := "box", runasUser := root, runasGroup := none,
    runasUserExplicit := false, command := .run "/bin/true" "/bin/true" [],
    now := 1710055800, fileIds := [("/bin/true", 1, 1)],
    localTimeBounds := [(1710037800, 1710055800), (1730597400, 1730615400)] }
def localWindow := "alice ALL = (root) NOTBEFORE=20240310023000 NOTAFTER=20241103013000 NOPASSWD: /bin/true\n"
def resolvedWindow := "alice ALL = (root) NOTBEFORE=20240310073000Z NOTAFTER=20241103063000Z NOPASSWD: /bin/true\n"

-- The spring gap and fall fold render the supplied epochs, never naive UTC.
#guard render localWindow false (some timeFacts) == some (
  "User alice may run the following commands on box:\n" ++
  "    (root) NOTBEFORE=20240310073000Z NOTAFTER=20241103063000Z NOPASSWD: /bin/true\n")
#guard render localWindow true (some timeFacts) == some (
  "User alice may run the following commands on box:\n\n" ++
  "Sudoers entry: /etc/sudoers.d/test\n    RunAsUsers: root\n" ++
  "    Options: !authenticate\n    NotBefore: 20240310073000Z\n" ++
  "    NotAfter: 20241103063000Z\n    Commands:\n\t/bin/true\n")
#guard render localWindow false (some timeFacts) == render resolvedWindow
#guard render localWindow true (some timeFacts) == render resolvedWindow true
-- Display is independent of the request clock (including its current DST season).
#guard render localWindow true (some { timeFacts with now := 0 }) ==
  render localWindow true (some timeFacts)
-- Zoned dates need no facts and ignore conflicting conversion entries.
#guard render resolvedWindow true (some { timeFacts with
  localTimeBounds := [(1710055800, 0), (1730615400, 0)] }) == render resolvedWindow true

-- An unresolved bound omits the entire spec, not just its date annotation.
#guard render localWindow == some "User alice is not allowed to run sudo on box.\n"
#guard render localWindow true == some "User alice is not allowed to run sudo on box.\n"
#guard render localWindow false (some { timeFacts with localTimeBounds := [(1710037800, 1710055800)] }) ==
  some "User alice is not allowed to run sudo on box.\n"
#guard render localWindow true (some { timeFacts with localTimeBounds := [(1730597400, 1730615400)] }) ==
  some "User alice is not allowed to run sudo on box.\n"
#guard render (localWindow ++ "alice ALL = (root) /bin/false\n") ==
  render "alice ALL = (root) /bin/false\n"

def renderCommand (text : String) (r : Request) (verbose : Bool := true) : Option String := do
  let located ← (parse "/etc/sudoers.d/test" text).toOption
  pure (listCommand (located.map (·.entry)) {} r located verbose)

#guard renderCommand localWindow timeFacts == renderCommand resolvedWindow timeFacts
#guard renderCommand localWindow timeFacts == some (
  "Sudoers entry: /etc/sudoers.d/test\n    RunAsUsers: root\n" ++
  "    Options: !authenticate\n    NotBefore: 20240310073000Z\n" ++
  "    NotAfter: 20241103063000Z\n    Commands:\n\t/bin/true\n    Matched: /bin/true\n")
#guard renderCommand localWindow timeFacts false == some "/bin/true\n"
#guard renderCommand localWindow { timeFacts with localTimeBounds := [] } == some ""
#guard renderCommand localWindow { timeFacts with localTimeBounds := [] } false == some ""
#guard renderCommand localWindow { timeFacts with now := 1710054900 } == some ""

end Tests.Listing
