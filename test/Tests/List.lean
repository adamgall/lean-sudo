import LeanSudo.Policy.List
import LeanSudo.Sudoers.Parser

namespace Tests.Listing
open LeanSudo LeanSudo.Sudoers LeanSudo.Policy

def alice : Principal := ⟨"alice", 1000, 1000, [], "/home/alice", "/bin/bash"⟩
def policy := "Cmnd_Alias SHELLS = /bin/sh, !/bin/bash\nRunas_Alias ADMINS = root, !daemon\nalice ALL = (ADMINS : root) SETENV: NOPASSWD: ALL, !SHELLS, (root) /bin/true, (root) /bin/false\n"
def render (text : String) (verbose : Bool := false) : Option String := do
  let located ← (parse "/etc/sudoers.d/test" text).toOption
  pure (listPrivileges (located.map (·.entry)) {} alice "box" id verbose located)

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

end Tests.Listing
