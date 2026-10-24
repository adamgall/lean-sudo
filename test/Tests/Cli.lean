import LeanSudo.Cli
import LeanSudo.CliProofs
import LeanSudo.Prompt

/-! Compile-time tests for `LeanSudo.Cli` and `LeanSudo.Prompt`. -/

namespace Tests.Cli

open LeanSudo LeanSudo.Cli

def P (args : List String) : Except String Options := parseArgs "sudo" args

def okOf : Except String Options → Option Options
  | .ok o => some o
  | .error _ => none

def errOf : Except String Options → Option String
  | .ok _ => none
  | .error e => some e

/-- error message without the trailing usage text -/
def msgOf (r : Except String Options) : Option String :=
  (errOf r).map fun e => (e.splitOn "\n").head!

def usageS : String := usageFor "sudo"

/-! ### Basic run mode -/
#guard okOf (P ["id"]) == some { command := ["id"] }
#guard okOf (P ["-u", "bob", "id", "-u"]) == some { user := some "bob", command := ["id", "-u"] }
#guard okOf (P ["-u", "#1000", "id"]) == some { user := some "#1000", command := ["id"] }

/-! ### Bundling -/
#guard okOf (P ["-iu", "bob"]) == some { login := true, user := some "bob" }
#guard okOf (P ["-ubob", "ls"]) == some { user := some "bob", command := ["ls"] }
#guard okOf (P ["-Hu", "bob", "ls", "-l"]) ==
  some { setHome := true, user := some "bob", command := ["ls", "-l"] }
#guard okOf (P ["-nbHP", "-g", "wheel", "ls"]) ==
  some { nonInteractive := true, background := true, setHome := true, preserveGroups := true,
         group := some "wheel", command := ["ls"] }
#guard okOf (P ["-Sp", "pw: ", "ls"]) == some { stdin := true, prompt := some "pw: ", command := ["ls"] }
#guard okOf (P ["-p", "", "ls"]) == some { prompt := some "", command := ["ls"] }
#guard okOf (P ["-C5", "-D", "/tmp", "-AB", "ls"]) ==
  some { closeFrom := some 5, chdir := some "/tmp", askpass := true, bell := true, command := ["ls"] }

/-! ### Long options -/
#guard okOf (P ["--user=bob", "ls"]) == some { user := some "bob", command := ["ls"] }
#guard okOf (P ["--user", "bob", "ls"]) == some { user := some "bob", command := ["ls"] }
#guard okOf (P ["--us", "bob", "ls"]) == some { user := some "bob", command := ["ls"] }
#guard okOf (P ["--login"]) == some { login := true }
#guard okOf (P ["--shell", "--set-home", "--non-interactive", "--background", "ls"]) ==
  some { shell := true, setHome := true, nonInteractive := true, background := true, command := ["ls"] }
#guard okOf (P ["--group=wheel", "--chdir=/", "--close-from=10", "--prompt=x", "--stdin", "ls"]) ==
  some { group := some "wheel", chdir := some "/", closeFrom := some 10, prompt := some "x",
         stdin := true, command := ["ls"] }
#guard okOf (P ["--preserve-groups", "--askpass", "--bell", "--no-update", "ls"]) ==
  some { preserveGroups := true, askpass := true, bell := true, noUpdate := true, command := ["ls"] }
#guard okOf (P ["--preserve-env", "ls"]) == some { preserveEnv := .all, command := ["ls"] }
#guard okOf (P ["--preserve-env=A,B", "--preserve-env=C", "ls"]) ==
  some { preserveEnv := .vars ["A", "B", "C"], command := ["ls"] }
#guard okOf (P ["-E", "--preserve-env=A", "ls"]) == some { preserveEnv := .all, command := ["ls"] }
#guard okOf (P ["--preserve-env=", "ls"]) == some { command := ["ls"] }
#guard msgOf (P ["--preserve-env=A=b", "ls"]) == some "invalid environment variable name: A=b"
-- `--preserve-env list`: the list is an operand (optional arguments must be attached)
#guard okOf (P ["--preserve-env", "A", "ls"]) == some { preserveEnv := .all, command := ["A", "ls"] }
#guard okOf (P ["--list"]) == some { mode := .list, listVerbose := 1 }
#guard okOf (P ["--validate"]) == some { mode := .validate }
#guard okOf (P ["--reset-timestamp"]) == some { mode := .resetTimestamp }
#guard okOf (P ["--remove-timestamp"]) == some { mode := .removeTimestamp }
#guard okOf (P ["--edit", "f"]) == some { mode := .edit, command := ["f"] }
#guard okOf (P ["--help"]) == some { mode := .help }
#guard okOf (P ["--version"]) == some { mode := .version }
#guard okOf (P ["--other-user", "bob", "-l"]) == some { mode := .list, listVerbose := 1, otherUser := some "bob" }
#guard msgOf (P ["--pre", "ls"]) ==
  some "option '--pre' is ambiguous; possibilities: '--preserve-env' '--preserve-groups'"
#guard msgOf (P ["--foo=1", "ls"]) == some "unrecognized option '--foo=1'"
#guard msgOf (P ["--login=yes"]) == some "option '--login' doesn't allow an argument"
#guard msgOf (P ["--user"]) == some "option '--user' requires an argument"

/-! ### `--` and operands -/
#guard okOf (P ["--", "-u", "ls"]) == some { command := ["-u", "ls"] }
#guard okOf (P ["-u", "bob", "--", "FOO=bar", "ls"]) == some { user := some "bob", command := ["FOO=bar", "ls"] }
#guard okOf (P ["ls", "-u", "bob", "--", "x"]) == some { command := ["ls", "-u", "bob", "--", "x"] }
#guard okOf (P ["-", "x"]) == some { command := ["-", "x"] }
#guard okOf (P ["FOO=bar", "-u", "bob", "BAR=", "ls", "A=b"]) ==
  some { envVars := [("FOO", "bar"), ("BAR", "")], user := some "bob", command := ["ls", "A=b"] }
#guard okOf (P ["/bin/x=y", "a"]) == some { command := ["/bin/x=y", "a"] }
#guard okOf (P ["=x", "a"]) == some { command := ["=x", "a"] }
#guard okOf (P ["A=1=2", "ls"]) == some { envVars := [("A", "1=2")], command := ["ls"] }

/-! ### Modes and conflicts -/
#guard errOf (P []) == some usageS
#guard errOf (P ["-i", "-s"]) == some ("you may not specify both the -i and -s options\n" ++ usageS)
#guard msgOf (P ["-i", "-E", "ls"]) == some "you may not specify both the -i and -E options"
#guard msgOf (P ["-l", "-v"]) == some "Only one of the -e, -h, -i, -K, -l, -s, -v or -V options may be specified"
#guard msgOf (P ["-e", "-l", "f"]) == some exclMsg
#guard okOf (P ["-K"]) == some { mode := .removeTimestamp }
#guard errOf (P ["-K", "ls"]) == some usageS
#guard errOf (P ["-K", "-u", "bob"]) == some usageS
#guard okOf (P ["-k"]) == some { mode := .resetTimestamp }
#guard okOf (P ["-k", "ls"]) == some { resetTimestamp := true, command := ["ls"] }
#guard okOf (P ["-ks"]) == some { resetTimestamp := true, shell := true }
#guard okOf (P ["-kv"]) == some { mode := .validate, resetTimestamp := true }
#guard okOf (P ["-kl"]) == some { mode := .list, listVerbose := 1, resetTimestamp := true }
#guard errOf (P ["-kn"]) == some usageS
#guard msgOf (P ["-k", "-N", "ls"]) == some exclTicketMsg
#guard msgOf (P ["-N", "-K"]) == some exclTicketMsg
#guard okOf (P ["-vn"]) == some { mode := .validate, nonInteractive := true }
#guard errOf (P ["-v", "ls"]) == some usageS
#guard errOf (P ["-vs"]) == some usageS
#guard okOf (P ["-ll"]) == some { mode := .list, listVerbose := 2 }
#guard okOf (P ["-l", "ls", "-a"]) == some { mode := .list, listVerbose := 1, command := ["ls", "-a"] }
#guard okOf (P ["-l", "-u", "bob", "ls"]) ==
  some { mode := .list, listVerbose := 1, user := some "bob", command := ["ls"] }
#guard errOf (P ["-l", "-u", "bob"]) == some usageS
#guard errOf (P ["-ls"]) == some usageS
#guard msgOf (P ["-U", "bob", "ls"]) == some "the -U option may only be used with the -l option"
#guard msgOf (P ["-A", "-S", "ls"]) == some "the -A and -S options may not be used together"
#guard errOf (P ["-e"]) == some usageS
#guard okOf (P ["-e", "/etc/hosts"]) == some { mode := .edit, command := ["/etc/hosts"] }
#guard msgOf (P ["-e", "-E", "f"]) == some "the -E option is not valid in edit mode"
#guard msgOf (P ["-e", "--preserve-env=A", "f"]) == some "you may not specify environment variables in edit mode"
#guard msgOf (P ["-e", "A=b", "f"]) == some "you may not specify environment variables in edit mode"
#guard errOf (P ["-e", "-i", "f"]) == some usageS
#guard errOf (P ["-e", "-s", "f"]) == some usageS
#guard okOf (P ["-h"]) == some { mode := .help }
#guard errOf (P ["-h", "-n"]) == some usageS
#guard msgOf (P ["-h", "host", "ls"]) == some "the -h (--host) option is not supported"
#guard msgOf (P ["-hhost", "ls"]) == some "the -h (--host) option is not supported"
#guard msgOf (P ["--host=x", "ls"]) == some "the -h (--host) option is not supported"
#guard okOf (P ["-V"]) == some { mode := .version }
#guard msgOf (P ["-V", "-h"]) == some exclMsg
#guard errOf (P ["-r", "role", "ls"]) == some usageS
#guard errOf (P ["-t", "type", "ls"]) == some usageS
#guard msgOf (P ["-R", "/", "ls"]) == some "you are not permitted to use the -R option"
#guard msgOf (P ["-T", "5", "ls"]) == some "you are not permitted to use the -T option"
#guard msgOf (P ["--chroot=/", "ls"]) == some "you are not permitted to use the -R option"
#guard msgOf (P ["-C", "2", "ls"]) == some "the argument to -C must be a number greater than or equal to 3"
#guard msgOf (P ["-C", "x", "ls"]) == some "the argument to -C must be a number greater than or equal to 3"
#guard msgOf (P ["-x"]) == some "invalid option -- 'x'"
#guard msgOf (P ["-u"]) == some "option requires an argument -- 'u'"
#guard errOf (P ["-u", "", "ls"]) == some usageS
#guard errOf (P ["-u", "a", "-u", "b", "ls"]) == some usageS

/-! ### sudoedit -/
#guard okOf (parseArgs "sudoedit" ["/etc/hosts", "/etc/motd"]) ==
  some { mode := .edit, command := ["/etc/hosts", "/etc/motd"] }
#guard okOf (parseArgs "sudoedit" ["-u", "bob", "-n", "f"]) ==
  some { mode := .edit, user := some "bob", nonInteractive := true, command := ["f"] }
#guard errOf (parseArgs "sudoedit" []) == some (usageFor "sudoedit")
#guard okOf (parseArgs "sudoedit" ["-h"]) == some { mode := .help }
#guard okOf (parseArgs "sudoedit" ["-V"]) == some { mode := .version }
#guard msgOf (parseArgs "sudoedit" ["-i", "f"]) == some "invalid option -- 'i'"
#guard msgOf (parseArgs "sudoedit" ["--shell", "f"]) == some "unrecognized option '--shell'"
-- `--login` is a unique prefix of `--login-class` for sudoedit (as with glibc), which is not
-- compiled in: plain usage
#guard errOf (parseArgs "sudoedit" ["--login", "f"]) == some (usageFor "sudoedit")
#guard basename "/usr/bin/sudoedit" == "sudoedit"
#guard basename "sudo" == "sudo"

/-! ### Messages -/
#guard formatError "sudo" "you may not specify both the -i and -s options\nusage: x\n" ==
  "sudo: you may not specify both the -i and -s options\nusage: x\n"
#guard formatError "sudo" usageS == usageS
#guard formatError "sudo" "the -h (--host) option is not supported" ==
  "sudo: the -h (--host) option is not supported\n"
#guard usageText == "usage: sudo -h | -K | -k | -V\nusage: sudo -v [-ABkNnS] [-g group] [-h host] [-p prompt] [-u user]\nusage: sudo -l [-ABkNnS] [-g group] [-h host] [-p prompt] [-U user]\n            [-u user] [command [arg ...]]\nusage: sudo [-ABbEHkNnPS] [-C num] [-D directory]\n            [-g group] [-h host] [-p prompt] [-R directory] [-T timeout]\n            [-u user] [VAR=value] [-i | -s] [command [arg ...]]\nusage: sudo -e [-ABkNnS] [-C num] [-D directory]\n            [-g group] [-h host] [-p prompt] [-R directory] [-T timeout]\n            [-u user] file ...\n"
#guard helpText == "sudo - execute a command as another user\n\nusage: sudo -h | -K | -k | -V\nusage: sudo -v [-ABkNnS] [-g group] [-h host] [-p prompt] [-u user]\nusage: sudo -l [-ABkNnS] [-g group] [-h host] [-p prompt] [-U user]\n            [-u user] [command [arg ...]]\nusage: sudo [-ABbEHkNnPS] [-C num] [-D directory]\n            [-g group] [-h host] [-p prompt] [-R directory] [-T timeout]\n            [-u user] [VAR=value] [-i | -s] [command [arg ...]]\nusage: sudo -e [-ABkNnS] [-C num] [-D directory]\n            [-g group] [-h host] [-p prompt] [-R directory] [-T timeout]\n            [-u user] file ...\n\nOptions:\n  -A, --askpass                 use a helper program for password prompting\n  -b, --background              run command in the background\n  -B, --bell                    ring bell when prompting\n  -C, --close-from=num          close all file descriptors >= num\n  -D, --chdir=directory         change the working directory before running\n                                command\n  -E, --preserve-env            preserve user environment when running command\n      --preserve-env=list       preserve specific environment variables\n  -e, --edit                    edit files instead of running a command\n  -g, --group=group             run command as the specified group name or ID\n  -H, --set-home                set HOME variable to target user's home dir\n  -h, --help                    display help message and exit\n  -h, --host=host               run command on host (if supported by plugin)\n  -i, --login                   run login shell as the target user; a command\n                                may also be specified\n  -K, --remove-timestamp        remove timestamp file completely\n  -k, --reset-timestamp         invalidate timestamp file\n  -l, --list                    list user's privileges or check a specific\n                                command; use twice for longer format\n  -n, --non-interactive         non-interactive mode, no prompts are used\n  -P, --preserve-groups         preserve group vector instead of setting to\n                                target's\n  -p, --prompt=prompt           use the specified password prompt\n  -R, --chroot=directory        change the root directory before running command\n  -S, --stdin                   read password from standard input\n  -s, --shell                   run shell as the target user; a command may\n                                also be specified\n  -T, --command-timeout=timeout terminate command after the specified time limit\n  -U, --other-user=user         in list mode, display privileges for user\n  -u, --user=user               run command (or edit file) as specified user\n                                name or ID\n  -V, --version                 display version information and exit\n  -v, --validate                update user's timestamp without running a\n                                command\n  --                            stop processing command line arguments\n"
#guard helpFor "sudoedit" == "sudoedit - edit files as another user\n\nusage: sudoedit -h | -V\nusage: sudoedit [-ABkNnS] [-C num] [-D directory]\n                [-g group] [-h host] [-p prompt] [-R directory] [-T timeout]\n                [-u user] file ...\n\nOptions:\n  -A, --askpass                 use a helper program for password prompting\n  -B, --bell                    ring bell when prompting\n  -C, --close-from=num          close all file descriptors >= num\n  -D, --chdir=directory         change the working directory before running\n                                command\n  -g, --group=group             run command as the specified group name or ID\n  -h, --help                    display help message and exit\n  -h, --host=host               run command on host (if supported by plugin)\n  -k, --reset-timestamp         invalidate timestamp file\n  -n, --non-interactive         non-interactive mode, no prompts are used\n  -p, --prompt=prompt           use the specified password prompt\n  -R, --chroot=directory        change the root directory before running command\n  -S, --stdin                   read password from standard input\n  -T, --command-timeout=timeout terminate command after the specified time limit\n  -u, --user=user               run command (or edit file) as specified user\n                                name or ID\n  -V, --version                 display version information and exit\n  --                            stop processing command line arguments\n"

/-! ### Shell mode -/
#guard shellCommand "/bin/bash" false [] == { path := "/bin/bash", argv := ["/bin/bash"] }
#guard shellCommand "/bin/bash" true [] == { path := "/bin/bash", argv := ["-bash"] }
#guard shellCommand "/bin/zsh" false ["echo", "a b;c", "$HOME", "x_y-z"] ==
  { path := "/bin/zsh", argv := ["/bin/zsh", "-c", "echo a\\ b\\;c $HOME x_y-z"] }
#guard shellCommand "/usr/bin/fish" true ["ls", "*.txt"] ==
  { path := "/usr/bin/fish", argv := ["-fish", "-c", "ls \\*\\.txt"] }
#guard shellEscape ["it's", "a\"b", "\n", "é"] == "it\\'s a\\\"b \\\n \\é"
#guard shellEscape ["`id`", "$(id)", "a|b&c>d<e"] == "\\`id\\` $\\(id\\) a\\|b\\&c\\>d\\<e"
example : WellEscaped (shellEscape ["rm", "-rf", "/; reboot"]).toList := shellEscape_wellEscaped _

/-! ### Theorems instantiated -/
example (o : Options) (h : parseArgs "sudo" ["--", "-i", "x"] = .ok o) : o.command = ["-i", "x"] :=
  parseArgs_dashdash h

/-! ### Prompt -/
#guard expandPrompt "[sudo] password for %p: " "alice" "root" "host" "alice" == "[sudo] password for alice: "
#guard expandPrompt "%u->%U@%h/%H %% %x %" "alice" "root" "box" "root" == "alice->root@box/box % %x %"
#guard expandPrompt "%%u" "a" "b" "c" "d" == "%u"
#guard expandPrompt "" "a" "b" "c" "d" == ""

end Tests.Cli
