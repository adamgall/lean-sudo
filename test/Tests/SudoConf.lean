import LeanSudo.SudoConf
import LeanSudo.Prompt
open LeanSudo

#guard (SudoConf.parse "# default configuration\n").toOption == some {}
#guard (SudoConf.parse "Plugin sudoers_policy sudoers.so\nPlugin sudoers_io sudoers.so\nPlugin sudoers_audit sudoers.so").isOk
#guard !(SudoConf.parse "Plugin approval_plugin approval.so").isOk
#guard !(SudoConf.parse "Plugin sudoers_policy /tmp/sudoers.so").isOk
#guard !(SudoConf.parse "Plugin sudoers_policy sudoers.so sudoers_file=/tmp/rules").isOk
#guard !(SudoConf.parse "Plugin sudoers_policy").isOk
#guard !(SudoConf.parse "Set group_source invented").isOk
#guard !(SudoConf.parse "Set max_groups 0").isOk
#guard !(SudoConf.parse "Set disable_coredump maybe").isOk
#guard !(SudoConf.parse "pLuGiN restricted_approval approval.so").isOk
#guard (SudoConf.parse "pAtH AsKpAsS /helper\nsEt group_source DYNAMIC").toOption.map
  (fun c => (c.askpass, c.groupSource)) == some (some "/helper", "dynamic")
#guard (SudoConf.parse "Path askpass /usr/bin/askpass\nPath noexec /lib/noexec.so\nSet disable_coredump false\nSet group_source dynamic\nSet max_groups 32\nSet probe_interfaces false").toOption == some {
  askpass := some "/usr/bin/askpass", noexec := some "/lib/noexec.so", disableCoredump := false
  groupSource := "dynamic", maxGroups := 32, probeInterfaces := false }
#guard (SudoConf.parse "Path askpass /one\nPath askpass\nPath noexec").toOption.map (fun c => (c.askpass, c.noexec)) == some (none, none)
#guard (SudoConf.parse "Path askpass \\\n/helper\nDebug sudo /tmp/debug all@debug").toOption.map (·.askpass) == some (some "/helper")
#guard expandPrompt "%h/%H %u %U %p %%" "alice" "root" "host.example.com" "alice" ==
  "host/host.example.com alice root alice %"

#guard SudoConf.fileProblem 1000 0o100666 == some "is owned by uid 1000, should be 0"
#guard SudoConf.fileProblem 0 0o100666 == some "is world writable"
#guard SudoConf.fileProblem 0 0o100664 == some "is group writable"
#guard SudoConf.fileProblem 0 0o040755 == some "is not a regular file"
#guard SudoConf.fileProblem 0 0o100644 == none
#guard (SudoConf.parseFile 0 0o100664 "Path noexec /nonexistent").toOption == some {}
#guard (SudoConf.parseFile 1000 0o100644 "Plugin evil /evil.so").toOption == some {}
#guard (SudoConf.parseFile 0 0o100666 "Plugin evil /evil.so").toOption == some {}
#guard !(SudoConf.parseFile 0 0o100644 "Plugin evil /evil.so").isOk
#guard (SudoConf.parseFile 0 0o100644 "Path noexec /safe").toOption.map (·.noexec) ==
  some (some "/safe")
