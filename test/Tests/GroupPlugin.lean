import LeanSudo.CoreProofs
import LeanSudo.Policy.Defaults
import LeanSudo.Sys.GroupPlugin

namespace Tests.GroupPlugin
open LeanSudo LeanSudo.Policy LeanSudo.Sudoers

private def alice : Principal := {
  name := "alice", uid := 1000, gid := 1000, groups := [("local", 1000)]
  home := "/home/alice", shell := "/bin/sh" }
private def root : Principal := { alice with name := "root", uid := 0, gid := 0, groups := [] }
private def st : Settings := { groupPlugin := some "group_file.so /etc/sudo-group" }
private def facts : Request := {
  user := alice, host := "host", runasUser := root, runasGroup := none
  runasUserExplicit := false, command := .run "/usr/bin/id" "/usr/bin/id" []
  pluginGroups := [("alice", "admins", true), ("alice", "#42", true),
    ("alice", "denied", false), ("root", "roots", true)] }

#guard userBase alice st (some facts) (.nonunixGroup "admins")
#guard !userBase alice st none (.nonunixGroup "admins")
#guard !userBase alice {} (some facts) (.nonunixGroup "admins")
#guard !userBase alice st (some facts) (.nonunixGroup "denied")
#guard !userBase alice st (some facts) (.nonunixGroup "missing")
#guard !userBase alice st (some facts) (.nonunixGroup "roots")
#guard !userBase root st (some facts) (.nonunixGroup "admins")
#guard !userBase alice st (some facts) (.nonunixGroup "ADMINS")
#guard !userBase alice st (some facts) (.nonunixGroup "local")
#guard userBase alice st (some facts) (.nonunixGid 42)
#guard !userBase alice st (some facts) (.nonunixGid 1000)
#guard !userBase alice st (some facts) (.group "admins")
#guard !userBase alice st (some facts) (.gid 42)
#guard userBase alice { st with alwaysQueryGroupPlugin := true } (some facts) (.group "admins")
#guard userBase alice { st with alwaysQueryGroupPlugin := true } (some facts) (.gid 42)
#guard userBase alice { st with alwaysQueryGroupPlugin := true } (some facts) (.group "local")
#guard userBase alice { st with alwaysQueryGroupPlugin := true } (some facts) (.gid 1000)
#guard !userBase alice { alwaysQueryGroupPlugin := true } (some facts) (.group "admins")
#guard userListResult {} 1 alice [{ atom := .all, negated := false }, { atom := .nonunixGroup "admins", negated := true }]
  st (some facts) == some false
#guard userListResult {} 1 alice [{ atom := .all, negated := false }, { atom := .nonunixGroup "denied", negated := true }]
  st (some facts) == some true
#guard userListResult {} 1 alice [{ atom := .nonunixGroup "denied", negated := true }]
  st (some facts) == none
#guard runasUserResult {} 1 root [{ atom := .nonunixGroup "roots", negated := false }] st (some facts) == some true

example (r : Request) (s : Settings) (u g : String)
    (h : pluginGroupMatch s (some r) u g = true) :
    (u, g, true) ∈ r.pluginGroups := by
  obtain ⟨r', hr, hm⟩ := pluginGroupMatch_requires_yes s (some r) u g h
  cases Option.some.inj hr
  exact hm

#guard Sys.GroupPlugin.splitConfig "group_file.so /etc/sudo-group" ==
  ("/usr/libexec/sudo/group_file.so", #["/etc/sudo-group"])
#guard Sys.GroupPlugin.splitConfig "/opt/provider.so\t one  two\t" ==
  ("/opt/provider.so", #["one", "two"])
#guard Sys.GroupPlugin.splitConfig "system_group.so" ==
  ("/usr/libexec/sudo/system_group.so", #[])

end Tests.GroupPlugin
