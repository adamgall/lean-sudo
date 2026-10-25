import LeanSudo.Intercept
import LeanSudo.Sudoers.Parser
import LeanSudo.Policy.Defaults

namespace Tests.Intercept
open LeanSudo

private def policy (text : String) : Sudoers.Sudoers :=
  (Sudoers.parse "sudoers" text).toOption.getD [] |>.map (·.entry)
private def alice : Principal := ⟨"alice", 1000, 1000, [("alice", 1000)], "/home/alice", "/bin/sh"⟩
private def root : Principal := ⟨"root", 0, 0, [("root", 0)], "/root", "/bin/sh"⟩
private def ctx : Core.Context := {
  progname := "sudo", opts := { command := ["/usr/bin/id"] }, invoking := alice,
  host := "box", sudoers := policy "alice ALL=(root) INTERCEPT: /bin/sh, NOINTERCEPT: /usr/bin/id\n",
  settings := {}, target := root, targetGroup := none, listUser := none,
  command := some ⟨"/usr/bin/id", "/usr/bin/id", "/usr/bin/id", []⟩,
  userEnv := [], cwd := "/", userUmask := 0o022, ttyName := none, canon := id,
  now := 1000000000, tsScope := .ppid 1 1, tsRecords := [],
  fileIds := [("/usr/bin/id", 1, 1), ("/bin/sh", 1, 2), ("/bin/rm", 1, 3)] }
private def rmCtx : Core.Context := { ctx with
  command := some ⟨"/bin/rm", "/bin/rm", "/bin/rm", ["/x"]⟩,
  opts := { command := ["/bin/rm", "/x"] } }

#guard (Intercept.decide ctx true false).allowed
#guard (Intercept.decide ctx true false).auth == .none
#guard !(Intercept.decide rmCtx true false).allowed
#guard (Intercept.decide rmCtx false false).allowed
#guard (Intercept.decide rmCtx false false).auth == .none
#guard !(Intercept.decide { ctx with target := alice } true false).allowed
#guard !(Intercept.decide { ctx with invoking := root } true false).allowed
#guard (Intercept.decide ctx true true).allowed
#guard !(Intercept.decide { ctx with settings := { interceptAllowSetid := false } } true true).allowed
#guard (Intercept.decide { ctx with settings := { interceptAllowSetid := false } } true false).allowed
#guard (Intercept.decide { ctx with settings := { interceptAllowSetid := false } } false true).allowed
#guard (Intercept.decide { ctx with settings := { interceptAuthenticate := true } } true false).auth == .required alice
#guard Intercept.environment #["LD_PRELOAD=/untrusted.so", "SUDO_USER=changed", "X=1"] ==
  #["LD_PRELOAD=/untrusted.so", "SUDO_USER=changed", "X=1"]

private def rootedCtx : Core.Context := { ctx with
  sudoers := policy "alice ALL=(root) CHROOT=/jail INTERCEPT: /usr/bin/id\n",
  rootFacts := [("/jail", {
    command := .run "/usr/bin/id" "/usr/bin/id" [], argv := ["/usr/bin/id"],
    found := true, fileIds := [("/usr/bin/id", 2, 1)] })] }
#guard (Intercept.decide rootedCtx true false).allowed
#guard !(Intercept.decide { rootedCtx with rootFacts := [] } true false).allowed
#guard !(Intercept.decide { rootedCtx with invoking := root } true false).allowed
#guard !(Intercept.decide { rootedCtx with target := alice } true false).allowed

private def defaults (text : String) : Settings :=
  match Policy.resolveDefaults (policy text) alice "box" (some root) none id with
  | .ok (st, _) => st
  | .error _ => {}
#guard !(defaults "Defaults intercept_type=dso\n").interceptAllowSetid
#guard (defaults "Defaults intercept_type=trace\n").interceptAllowSetid
#guard (defaults "Defaults intercept_allow_setid, intercept_type=dso\n").interceptAllowSetid
#guard (defaults "Defaults intercept_type=dso, intercept_allow_setid\n").interceptAllowSetid
#guard !(defaults "Defaults !intercept_allow_setid, intercept_type=trace\n").interceptAllowSetid

end Tests.Intercept
