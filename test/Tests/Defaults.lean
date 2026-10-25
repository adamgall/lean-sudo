import LeanSudo.Policy.Defaults

namespace Tests.Defaults
open LeanSudo LeanSudo.Sudoers LeanSudo.Policy

def setting (name : String) (op : DefaultsOp) : Option Settings :=
  (applySetting {} { name, op }).toOption.map (·.1)

def error (name : String) (op : DefaultsOp) : Option String :=
  match applySetting {} { name, op } with | .error e => some e | .ok _ => none

#guard defaultOptionNames.length == 163
#guard defaultOptionNames.all (fun n => (defaultKind n).isSome)
#guard ({} : Settings).usePty
#guard ({} : Settings).fqdn
#guard ({} : Settings).caseInsensitiveUser && ({} : Settings).caseInsensitiveGroup
#guard ({} : Settings).envKeep.contains "DPKG_COLORS"
#guard ({} : Settings).editor == "/usr/bin/editor"
#guard ({} : Settings).rlimitCore == some "0,0"
#guard ({} : Settings).passwdTimeout == some 0
#guard ({} : Settings).lecture == "never"
#guard ({} : Settings).adminFlag == some "~/.sudo_as_admin_successful"
#guard (setting "intercept" (.flag true)).map (·.intercept) == some true
#guard (setting "group_plugin" (.assign "/usr/lib/plugin.so")).map (·.groupPlugin) == some (some "/usr/lib/plugin.so")
#guard (setting "rlimit_core" (.assign "infinity,1024")).map (·.rlimitCore) == some (some "infinity,1024")
#guard (setting "rlimit_core" (.flag false)).map (·.rlimitCore) == some none
#guard (setting "rlimit_as" (.assign "user")).map (·.rlimitAs) == some (some "user")
#guard error "rlimit_core" (.assign "unlimited") == some "value \"unlimited\" is invalid for option \"rlimit_core\""
#guard (setting "command_timeout" (.assign "1h2m3s")).map (·.commandTimeout) == some 3723
#guard (setting "command_timeout" (.flag false)).map (·.commandTimeout) == some 0
#guard error "command_timeout" (.assign "2147483648") |>.isSome
#guard (setting "passwd_timeout" (.assign "+2.5")).map (·.passwdTimeout) == some (some 150)
#guard (setting "closefrom" (.assign "-1")).map (·.closefrom) == some (-1)
#guard error "closefrom" (.assign "2147483648") |>.isSome
#guard error "passwd_tries" (.assign "4294967296") |>.isSome
#guard (setting "lecture" (.flag true)).map (·.lecture) == some "once"
#guard (setting "listpw" (.flag true)).map (·.listpw) == some .any
#guard (setting "verifypw" (.flag true)).map (·.verifypw) == some .all
#guard (setting "fdexec" (.flag true)).map (·.fdexec) == some "digest_only"
#guard error "timestamp_type" (.flag false) == some "no value specified for \"timestamp_type\""
#guard error "env_file" (.assign "relative") == some "values for \"env_file\" must start with a '/'"
#guard (setting "runcwd" (.assign "~alice")).map (·.runcwd) == some (some "~alice")
#guard error "pam_silent" (.assign "yes") == some "option \"pam_silent\" does not take a value"
#guard error "logfile" (.add "/tmp/log") == some "invalid operator \"+=\" for \"logfile\""
#guard (setting "passprompt_regex" (.assign "Password: *")).map (·.passpromptRegex) == some ["Password: *"]
#guard (setting "log_passwords" (.flag false)).map (·.logPasswords) == some false
#guard (applySetting { ignoreUnknownDefaults := true } { name := "future_option", op := .flag true }).toOption.map (·.2) == some none
#guard (applySetting {} { name := "future_option", op := .flag true }).toOption.map (·.2) == some (some "unknown defaults entry \"future_option\"")

#guard (setting "log_input" (.flag true)).map (fun s => (s.logStdin, s.logTtyin)) == some (true, true)
#guard (applySettings {} [{ name := "log_input", op := .flag true }, { name := "log_stdin", op := .flag false }]).toOption.map
  (fun (s, _) => (s.logStdin, s.logTtyin)) == some (false, true)
#guard (setting "maxseq" (.assign "-1")).map (·.maxseq) == some "2176782335"
#guard error "maxseq" (.assign "ZZZZZZ") |>.isSome
#guard parseTimeout "0.001" == some (some 0)
#guard ({} : Settings).syslogMaxlen == 960
#guard (setting "syslog_goodpri" (.assign "none")).map (·.syslogGoodpri) == some none
#guard (applySetting {} { name := "maxseq", op := .assign "not-a-number" } false).toOption.isSome
#guard !({} : Settings).passpromptConfigured
#guard !({} : Settings).badpassMessageConfigured
#guard (setting "passprompt" (.assign "[sudo] password for %p: ")).map
  (·.passpromptConfigured) == some true
#guard (setting "badpass_message" (.assign "Sorry, try again.")).map
  (·.badpassMessageConfigured) == some true

private def invoking : Principal := ⟨"alice", 1000, 1000, [], "/home/alice", "/bin/sh"⟩

#guard (resolveDefaults [] invoking "box" none none
  (initial := { passpromptOverride := true })).toOption.map
  (fun (s, _) => s.passpromptOverride) == some true
#guard (resolveDefaults [.defaults .global [{ name := "passprompt_override", op := .flag false }]]
  invoking "box" none none (initial := { passpromptOverride := true })).toOption.map
  (fun (s, _) => s.passpromptOverride) == some false

private def chrootWarning := "\"runchroot\" is deprecated and will be removed in a future sudo release"
#guard (applySetting {} { name := "runchroot", op := .assign "/" } (verbose := true)).toOption.map (·.2) == some (some chrootWarning)
#guard (applySetting {} { name := "runchroot", op := .flag false } (verbose := true)).toOption.map (·.2) == some (some chrootWarning)
#guard (applySetting {} { name := "runchroot", op := .assign "/" } false true).toOption.map (·.2) == some none
#guard (applySetting {} { name := "runchroot", op := .assign "/" }).toOption.map (·.2) == some none
#guard (applySetting {} { name := "runchroot", op := .assign "/tmp", source := some ("/tmp/deprecated-policy", 1, 25) } (verbose := true)).toOption.map (·.2) ==
  some (some ("/tmp/deprecated-policy:1:25: " ++ chrootWarning))
#guard error "runchroot" (.assign "relative") == some "values for \"runchroot\" must start with a '/', '~', or '*'"
#guard error "runchroot" (.flag true) == some "no value specified for \"runchroot\""
#guard (resolveDefaults [.defaults (.user [⟨false, .name "nobody"⟩]) [{ name := "runchroot", op := .assign "/" }]]
  invoking "box" none none (verbose := true)).toOption.map (·.2) == some []

end Tests.Defaults
