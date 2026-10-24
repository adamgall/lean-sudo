import LeanSudo.Visudo.Core

/-! Compile-time tests for `LeanSudo.Visudo.Core` (argument parsing and checks). -/

namespace Tests.Visudo

open LeanSudo.Sudoers LeanSudo.Visudo

def args (as : List String) : Option Options :=
  match parseArgs as with
  | .ok o => some o
  | .error _ => none

def argErr (as : List String) : Option String :=
  match parseArgs as with
  | .ok _ => none
  | .error e => some e

#guard args [] == some {}
#guard args ["-c"] == some { check := true }
#guard args ["-cqs"] == some { check := true, quiet := true, strict := true }
#guard args ["-cf", "x"] == some { check := true, file := some "x" }
#guard args ["-fx", "-c"] == some { check := true, file := some "x" }
#guard args ["--file=x", "--check"] == some { check := true, file := some "x" }
#guard args ["--file", "x", "--che"] == some { check := true, file := some "x" }
#guard args ["x", "-c"] == some { check := true, file := some "x" }
#guard args ["-c", "--", "-x"] == some { check := true, file := some "-x" }
#guard args ["-c", "-f", "-"] == some { check := true, file := some "-" }
#guard args ["-O", "-P", "-I"] == some { owner := true, perms := true, noIncludes := true }
#guard argErr ["-z"] == some "invalid option -- 'z'"
#guard argErr ["-c", "-f"] == some "option requires an argument -- 'f'"
#guard argErr ["--file"] == some "option '--file' requires an argument"
#guard argErr ["--check=1"] == some "option '--check' doesn't allow an argument"
#guard argErr ["--bogus"] == some "unrecognized option '--bogus'"
#guard argErr ["a", "b"] == some ""
#guard args ["-f", "a", "b"] == some { file := some "a" }
#guard args ["-xout", "-f", "in"] == some { file := some "in", exportFile := some "out" }
#guard args ["--export=out"] == some { exportFile := some "out" }
#guard argErr ["-x"] == some "option requires an argument -- 'x'"

def errorsOf (t : String) : List String :=
  match parse "s" t with
  | .ok es => semanticErrors es true
  | .error e => [e.toString]

def warningsOf (t : String) : List String :=
  match parse "s" t with
  | .ok es => unusedWarnings es
  | .error e => [e.toString]

#guard errorsOf "root ALL=(ALL:ALL) ALL\n" == []
#guard errorsOf "User_Alias A = bob\nUser_Alias A = carol\nA ALL = ALL\n" ==
  ["s:2: duplicate User_Alias \"A\", previously defined at s:1"]
#guard errorsOf "bob FOO = /usr/bin/id\n" == ["s:1: Host_Alias \"FOO\" referenced but not defined"]
#guard errorsOf "User_Alias A = B\nUser_Alias B = A\nA ALL = ALL\n" == ["s:2: cycle in User_Alias \"A\""]
#guard errorsOf "Defaults passwd_tries=abc\n" ==
  ["s:1: value \"abc\" is invalid for option \"passwd_tries\""]
#guard errorsOf "Defaults foobar\n" == ["s:1: unknown defaults entry \"foobar\""]
#guard errorsOf "Defaults mail_badpass\n" == []
#guard errorsOf "Defaults set_logname, !set_home\n" == []
#guard errorsOf "Defaults noexec\n" == []
#guard warningsOf "Cmnd_Alias C = /bin/ls\nroot ALL = ALL\n" == ["Warning: s:1: unused Cmnd_Alias \"C\""]
#guard warningsOf "Cmnd_Alias C = /bin/ls\nroot ALL = C\n" == []

#guard (parse "s" "bob FOO = /usr/bin/id\n").toOption.map (semanticErrors · false) ==
  some ["s:1: Host_Alias \"FOO\" referenced but not defined"]

/-- Neither mode may accept a policy that would disable the runtime. -/
def refusesRuntimeInvalid (text : String) : Bool :=
  match parse "s" text with
  | .error _ => false
  | .ok entries =>
    match LeanSudo.Policy.validate (entries.map (·.entry)) with
    | .ok () => false
    | .error _ => [false, true].all fun strict => !(semanticErrors entries strict).isEmpty

#guard ["bob FOO = /usr/bin/id\n",
  "User_Alias A = MISSING\nroot ALL=ALL\n",
  "User_Alias A = B\nUser_Alias B = A\nroot ALL=ALL\n",
  "Defaults:UNKNOWN !authenticate\nroot ALL=ALL\n",
  "Cmnd_Alias C = /bin/ls\nCmnd_Alias C = /bin/cat\nroot ALL=ALL\n"].all refusesRuntimeInvalid

#guard renderSyntaxError { file := "s", line := 2, col := 5, msg := "" } "a\nfoo bar\n" ==
  "s:2:5: syntax error\nfoo bar\n    ^~~"
#guard renderSyntaxError { file := "s", line := 1, col := 3, msg := "" } "\tx y\n" ==
  "s:1:3: syntax error\n\tx y\n\t ^"
#guard renderSyntaxError { file := "s", line := 9, col := 1, msg := "" } "a\n" == "s:9:1: syntax error"
#guard renderSyntaxError { file := "s", line := 1, col := 9, msg := "expected '=', found 'b'" }
    "foo bar baz\n" == "s:1:9: syntax error\nfoo bar baz\n        ^~~"

#guard envEditorValues [("EDITOR", "vi"), ("VISUAL", " "), ("SUDO_EDITOR", "nano -w")] ==
  ["nano -w", "vi"]
#guard whatNowChoice "e\n" == some 'e'
#guard whatNowChoice "Q" == some 'Q'
#guard whatNowChoice "q\n" == none
#guard withFinalNewline "a" == "a\n"
#guard withFinalNewline "" == ""

end Tests.Visudo
