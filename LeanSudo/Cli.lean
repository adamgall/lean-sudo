/-!
# Command-line parsing (`sudo` / `sudoedit`)

A pure re-implementation of sudo 1.9's `parse_args.c` on top of a GNU
`getopt_long`-compatible scanner (short-option bundling, `+` = stop at the first
operand, unique-prefix long options, `--`), including sudo's interleaving of
`VAR=value` operands with options.

Error convention: `parseArgs` returns `.error e` where `e` is exactly what sudo would
write to stderr *after* the leading `sudo: ` of its first line. Pure usage errors
(where sudo prints only the usage text) start with `usage:`. Use `formatError` to get
the complete stderr text.
-/

namespace LeanSudo.Cli

inductive Mode where
  | run | edit | list | validate | resetTimestamp | removeTimestamp | help | version
  deriving Repr, DecidableEq, Inhabited

inductive PreserveEnv where
  /-- no `-E` / `--preserve-env` -/
  | none
  /-- `-E` / `--preserve-env` without a list -/
  | all
  /-- `--preserve-env=a,b` (accumulated over all occurrences) -/
  | vars (vs : List String)
  deriving Repr, DecidableEq, Inhabited

structure Options where
  mode : Mode := .run
  /-- `-u user` (may be `#uid`) -/
  user : Option String := none
  /-- `-g group` (may be `#gid`) -/
  group : Option String := none
  /-- `-U user` (list mode only) -/
  otherUser : Option String := none
  /-- `-i` -/
  login : Bool := false
  /-- `-s` -/
  shell : Bool := false
  preserveEnv : PreserveEnv := .none
  /-- `-H` -/
  setHome : Bool := false
  /-- `-n` -/
  nonInteractive : Bool := false
  /-- `-S` -/
  stdin : Bool := false
  /-- `-p prompt` (may be empty) -/
  prompt : Option String := none
  /-- `-b` -/
  background : Bool := false
  /-- `-k` used as a flag together with a command, `-v`, `-l`, `-s`/`-i` or `-e` -/
  resetTimestamp : Bool := false
  /-- `-D dir` -/
  chdir : Option String := none
  /-- number of `-l` options -/
  listVerbose : Nat := 0
  /-- `-P` -/
  preserveGroups : Bool := false
  /-- `-B` (accepted; ring the bell when prompting) -/
  bell : Bool := false
  /-- `-C n`, `n ≥ 3` -/
  closeFrom : Option Nat := none
  /-- `-A` -/
  askpass : Bool := false
  /-- `-N`: do not update the timestamp -/
  noUpdate : Bool := false
  /-- `NAME=value` operands given before the command, in order -/
  envVars : List (String × String) := []
  /-- operands after option processing (the command and its arguments, or the files
  for `-e`/`sudoedit`, or the command to check for `-l`) -/
  command : List String := []
  deriving Repr, DecidableEq, Inhabited

/-! ## Usage, help and version text -/

/-- `basename` of `argv[0]` (sudo's `getprogname()`). -/
def basename (path : String) : String :=
  String.ofList ((path.toList.reverse.takeWhile (· != '/')).reverse)

private def sudoUsage : List (List String) :=
  [ ["-h | -K | -k | -V"],
    ["-v [-ABkNnS] [-g group] [-h host] [-p prompt] [-u user]"],
    ["-l [-ABkNnS] [-g group] [-h host] [-p prompt] [-U user]",
     "[-u user] [command [arg ...]]"],
    ["[-ABbEHkNnPS] [-C num] [-D directory]",
     "[-g group] [-h host] [-p prompt] [-R directory] [-T timeout]",
     "[-u user] [VAR=value] [-i | -s] [command [arg ...]]"],
    ["-e [-ABkNnS] [-C num] [-D directory]",
     "[-g group] [-h host] [-p prompt] [-R directory] [-T timeout]",
     "[-u user] file ..."] ]

private def sudoeditUsage : List (List String) :=
  [ ["-h | -V"],
    ["[-ABkNnS] [-C num] [-D directory]",
     "[-g group] [-h host] [-p prompt] [-R directory] [-T timeout]",
     "[-u user] file ..."] ]

/-- sudo's `display_usage` for the given program name (`sudo` or `sudoedit`). -/
def usageFor (progname : String) : String :=
  let vecs := if progname == "sudoedit" then sudoeditUsage else sudoUsage
  let ind := String.ofList (List.replicate (progname.length + 8) ' ')
  String.join <| vecs.map fun
    | [] => ""
    | first :: rest =>
      s!"usage: {progname} {first}\n" ++ String.join (rest.map fun l => ind ++ l ++ "\n")

def usageText : String := usageFor "sudo"

/-- Word wrapping as done by sudo's `sudo_lbuf_println` (80 columns, continuation
lines indented by `indent`). `fuel` bounds the number of output lines. -/
private def wrapAux (indent : Nat) : Nat → Nat → List Char → List Char
  | 0, _, _ => []
  | fuel + 1, avail, cs =>
    if cs.length ≤ avail then cs ++ ['\n'] else
      -- last space strictly before position `avail`, else first space after it
      let firstPart := cs.take avail
      let brk : Option Nat :=
        match (firstPart.reverse.findIdx? (· == ' ')) with
        | some j => some (avail - 1 - j)
        | none => ((cs.drop avail).findIdx? (· == ' ')).map (· + avail)
      match brk with
      | none => cs ++ ['\n']
      | some n =>
        let rest := (cs.drop n).dropWhile (fun c => c == ' ' || c == '\t')
        if rest.isEmpty then cs.take n ++ ['\n'] else
        cs.take n ++ ['\n'] ++ List.replicate indent ' ' ++ wrapAux indent fuel (80 - indent) rest

private def wrapLine (s : String) : String :=
  String.ofList (wrapAux 32 (s.length + 1) 80 s.toList)

private def helpEntries (sudoedit : Bool) : List String :=
  let both (l : String) := [l]
  let sudoOnly (l : String) := if sudoedit then [] else [l]
  both     "  -A, --askpass                 use a helper program for password prompting" ++
  sudoOnly "  -b, --background              run command in the background" ++
  both     "  -B, --bell                    ring bell when prompting" ++
  both     "  -C, --close-from=num          close all file descriptors >= num" ++
  both     "  -D, --chdir=directory         change the working directory before running command" ++
  sudoOnly "  -E, --preserve-env            preserve user environment when running command" ++
  sudoOnly "      --preserve-env=list       preserve specific environment variables" ++
  sudoOnly "  -e, --edit                    edit files instead of running a command" ++
  both     "  -g, --group=group             run command as the specified group name or ID" ++
  sudoOnly "  -H, --set-home                set HOME variable to target user's home dir" ++
  both     "  -h, --help                    display help message and exit" ++
  both     "  -h, --host=host               run command on host (if supported by plugin)" ++
  sudoOnly "  -i, --login                   run login shell as the target user; a command may also be specified" ++
  sudoOnly "  -K, --remove-timestamp        remove timestamp file completely" ++
  both     "  -k, --reset-timestamp         invalidate timestamp file" ++
  sudoOnly "  -l, --list                    list user's privileges or check a specific command; use twice for longer format" ++
  both     "  -n, --non-interactive         non-interactive mode, no prompts are used" ++
  sudoOnly "  -P, --preserve-groups         preserve group vector instead of setting to target's" ++
  both     "  -p, --prompt=prompt           use the specified password prompt" ++
  both     "  -R, --chroot=directory        change the root directory before running command" ++
  both     "  -S, --stdin                   read password from standard input" ++
  sudoOnly "  -s, --shell                   run shell as the target user; a command may also be specified" ++
  both     "  -T, --command-timeout=timeout terminate command after the specified time limit" ++
  sudoOnly "  -U, --other-user=user         in list mode, display privileges for user" ++
  both     "  -u, --user=user               run command (or edit file) as specified user name or ID" ++
  both     "  -V, --version                 display version information and exit" ++
  sudoOnly "  -v, --validate                update user's timestamp without running a command" ++
  both     "  --                            stop processing command line arguments"

/-- Output of `sudo -h` (to stdout, exit status 0). -/
def helpFor (progname : String) : String :=
  let sudoedit := progname == "sudoedit"
  let header := if sudoedit then s!"{progname} - edit files as another user\n\n"
    else s!"{progname} - execute a command as another user\n\n"
  header ++ usageFor progname ++ "\nOptions:\n" ++
    String.join ((helpEntries sudoedit).map wrapLine)

def helpText : String := helpFor "sudo"

/-- Output of `sudo -V`. -/
def versionText : String :=
  "Sudo version 1.9.16 (lean-sudo 0.1.0)\n" ++
  "Sudoers policy plugin version 1.9.16 (lean-sudo 0.1.0)\n" ++
  "Sudoers file grammar version 50\n"

/-- Complete stderr text for a `parseArgs` error. -/
def formatError (progname : String) (e : String) : String :=
  let body := if "usage:".toList.isPrefixOf e.toList then e else progname ++ ": " ++ e
  if body.toList.getLast? == some '\n' then body else body ++ "\n"

/-! ## Option scanner -/

/-- Argument requirement of an option. -/
inductive ArgSpec where
  | no | req | opt
  deriving Repr, DecidableEq, Inhabited

/-- sudo's short option string `+Aa:BbC:c:D:Eeg:Hh::iKklNnPp:R:r:SsT:t:U:u:Vv`
(and the restricted `sudoedit` one). `none` = not an option. -/
def shortSpec (sudoedit : Bool) (c : Char) : Option ArgSpec :=
  match c with
  | 'A' | 'B' | 'K' | 'k' | 'N' | 'n' | 'S' | 'V' => some .no
  | 'a' | 'C' | 'c' | 'D' | 'g' | 'p' | 'R' | 'r' | 'T' | 't' | 'u' => some .req
  | 'h' => some .opt
  | 'b' | 'E' | 'e' | 'H' | 'i' | 'l' | 'P' | 's' | 'v' => if sudoedit then none else some .no
  | 'U' => if sudoedit then none else some .req
  | _ => none

structure LongOpt where
  name : String
  spec : ArgSpec
  /-- equivalent short option; `#` stands for sudo's `OPT_HOSTNAME` (`--host`) -/
  key : Char
  /-- not available as `sudoedit` -/
  sudoOnly : Bool

/-- sudo's `sudo_long_opts` table, in order. -/
def longOpts : List LongOpt :=
  [ ⟨"background", .no, 'b', true⟩, ⟨"preserve-env", .opt, 'E', true⟩,
    ⟨"edit", .no, 'e', true⟩, ⟨"set-home", .no, 'H', true⟩, ⟨"login", .no, 'i', true⟩,
    ⟨"remove-timestamp", .no, 'K', true⟩, ⟨"list", .no, 'l', true⟩,
    ⟨"preserve-groups", .no, 'P', true⟩, ⟨"shell", .no, 's', true⟩,
    ⟨"other-user", .req, 'U', true⟩, ⟨"validate", .no, 'v', true⟩,
    ⟨"askpass", .no, 'A', false⟩, ⟨"auth-type", .req, 'a', false⟩, ⟨"bell", .no, 'B', false⟩,
    ⟨"close-from", .req, 'C', false⟩, ⟨"login-class", .req, 'c', false⟩,
    ⟨"chdir", .req, 'D', false⟩, ⟨"group", .req, 'g', false⟩, ⟨"help", .no, 'h', false⟩,
    ⟨"host", .req, '#', false⟩, ⟨"reset-timestamp", .no, 'k', false⟩,
    ⟨"no-update", .no, 'N', false⟩, ⟨"non-interactive", .no, 'n', false⟩,
    ⟨"prompt", .req, 'p', false⟩, ⟨"chroot", .req, 'R', false⟩, ⟨"role", .req, 'r', false⟩,
    ⟨"stdin", .no, 'S', false⟩, ⟨"command-timeout", .req, 'T', false⟩,
    ⟨"type", .req, 't', false⟩, ⟨"user", .req, 'u', false⟩, ⟨"version", .no, 'V', false⟩ ]

/-- sudo's `is_envar`: does not start with `/` or `=` and contains `=`. -/
def isEnvarL : List Char → Bool
  | [] => false
  | '/' :: _ => false
  | '=' :: _ => false
  | l => l.contains '='

def isEnvar (s : String) : Bool := isEnvarL s.toList

/-- Parser state (the settings sudo's `parse_args` accumulates). -/
structure Raw where
  progname : String
  sudoedit : Bool
  mode : Option Mode := none
  lcount : Nat := 0
  /-- `-k` or `-K` seen (`ARG_IGNORE_TICKET`) -/
  ignoreTicket : Bool := false
  noUpdate : Bool := false
  background : Bool := false
  preserveAll : Bool := false
  preserveVars : List String := []
  resetHome : Bool := false
  login : Bool := false
  nonInteractive : Bool := false
  preserveGroups : Bool := false
  shell : Bool := false
  envVars : List (String × String) := []
  user : Option String := none
  group : Option String := none
  otherUser : Option String := none
  prompt : Option String := none
  chdir : Option String := none
  closeFrom : Option Nat := none
  askpass : Bool := false
  stdin : Bool := false
  bell : Bool := false

def Raw.init (progname : String) : Raw :=
  let se := progname == "sudoedit"
  { progname, sudoedit := se, mode := if se then some .edit else none }

/-- `msg` followed by the usage text (sudo's `sudo_warnx(msg); usage()`). -/
def usageErr (r : Raw) (msg : String) : String := msg ++ "\n" ++ usageFor r.progname

def exclMsg : String :=
  "Only one of the -e, -h, -i, -K, -l, -s, -v or -V options may be specified"

def exclTicketMsg : String := "Only one of the -K, -k or -N options may be specified"

/-- Split `NAME=value` at the first `=`. -/
def splitEnvar (s : String) : String × String :=
  let l := s.toList
  (String.ofList (l.takeWhile (· != '=')), String.ofList ((l.dropWhile (· != '=')).drop 1))

/-- `strtok(list, ",")`: comma separated, empty tokens skipped. -/
def splitCommas (s : String) : List String :=
  (s.splitOn ",").filter (fun t => !t.isEmpty)

/-- `sudo_strtonum(s, 3, INT_MAX)` restricted to plain decimal digits. -/
def parseCloseFrom (s : String) : Option Nat :=
  if !s.isEmpty && s.toList.all Char.isDigit then
    let n := s.toNat!
    if 3 ≤ n && n ≤ 2147483647 then some n else none
  else none

/-- Apply one recognised option (`key` as in sudo's `switch (ch)`). -/
def applyOpt (r : Raw) (key : Char) (arg : Option String) : Except String Raw :=
  let usage : Except String Raw := .error (usageFor r.progname)
  let excl : Except String Raw := .error (usageErr r exclMsg)
  let exclTicket : Except String Raw := .error (usageErr r exclTicketMsg)
  let nonEmpty (k : String → Except String Raw) : Except String Raw :=
    match arg with
    | some a => if a.isEmpty then usage else k a
    | none => usage
  match key with
  | 'A' => .ok { r with askpass := true }
  | 'b' => .ok { r with background := true }
  | 'B' => .ok { r with bell := true }
  | 'C' =>
    match arg.bind parseCloseFrom with
    | none => .error (usageErr r "the argument to -C must be a number greater than or equal to 3")
    | some n => if r.closeFrom.isSome then usage else .ok { r with closeFrom := some n }
  | 'D' => nonEmpty fun a => if r.chdir.isSome then usage else .ok { r with chdir := some a }
  | 'E' =>
    match arg with
    | none => .ok { r with preserveAll := true }
    | some l =>
      let names := splitCommas l
      match names.find? (fun n => n.toList.contains '=') with
      | some bad => .error (usageErr r s!"invalid environment variable name: {bad}")
      | none => .ok { r with preserveVars := r.preserveVars ++ names }
  | 'e' =>
    if r.mode.isSome && r.mode != some .edit then excl else .ok { r with mode := some .edit }
  | 'g' => nonEmpty fun a => if r.group.isSome then usage else .ok { r with group := some a }
  | 'H' => .ok { r with resetHome := true }
  | 'h' =>
    match arg with
    | some _ => .error "the -h (--host) option is not supported"
    | none =>
      if r.mode.isSome && r.mode != some .help && !r.sudoedit then excl
      else .ok { r with mode := some .help }
  | '#' => .error "the -h (--host) option is not supported"
  | 'i' => .ok { r with login := true }
  | 'K' =>
    if r.mode.isSome && r.mode != some .removeTimestamp then excl
    else if r.noUpdate then exclTicket
    else .ok { r with mode := some .removeTimestamp, ignoreTicket := true }
  | 'k' => if r.noUpdate then exclTicket else .ok { r with ignoreTicket := true }
  | 'l' =>
    if r.mode.isSome && r.mode != some .list then excl
    else .ok { r with mode := some .list, lcount := r.lcount + 1 }
  | 'N' => if r.ignoreTicket then exclTicket else .ok { r with noUpdate := true }
  | 'n' => .ok { r with nonInteractive := true }
  | 'P' => .ok { r with preserveGroups := true }
  | 'p' =>
    match arg with
    | some a => if r.prompt.isSome then usage else .ok { r with prompt := some a }
    | none => usage
  | 'R' => .error "you are not permitted to use the -R option"
  | 'T' => .error "you are not permitted to use the -T option"
  | 'S' => .ok { r with stdin := true }
  | 's' => .ok { r with shell := true }
  | 'U' => nonEmpty fun a => if r.otherUser.isSome then usage else .ok { r with otherUser := some a }
  | 'u' => nonEmpty fun a => if r.user.isSome then usage else .ok { r with user := some a }
  | 'v' =>
    if r.mode.isSome && r.mode != some .validate then excl else .ok { r with mode := some .validate }
  | 'V' =>
    if r.mode.isSome && r.mode != some .version && !r.sudoedit then excl
    else .ok { r with mode := some .version }
  -- `-a`, `-c`, `-r`, `-t`: BSD auth / login class / SELinux are not compiled in
  | _ => usage

/-- Process a bundle of short options (the characters after the leading `-`).
`next` is the following command-line argument, `alone` whether the whole argument
was exactly `-h`. Returns the new state and whether `next` was consumed. -/
def shortCluster (r : Raw) (next : Option String) (alone : Bool) :
    List Char → Except String (Raw × Bool)
  | [] => .ok (r, false)
  | c :: cs =>
    match shortSpec r.sudoedit c with
    | none => .error (usageErr r s!"invalid option -- '{c}'")
    | some .no => do
      let r' ← applyOpt r c none
      shortCluster r' next alone cs
    | some .req =>
      if cs.isEmpty then
        match next with
        | some a => do return (← applyOpt r c (some a), true)
        | none => .error (usageErr r s!"option requires an argument -- '{c}'")
      else do return (← applyOpt r c (some (String.ofList cs)), false)
    | some .opt =>
      -- only `-h` has an optional argument; it must be attached (`-hhost`), except
      -- that a lone `-h` followed by a non-option, non-`VAR=value` word takes it
      if cs.isEmpty then
        match next with
        | some a =>
          if alone && a.toList.head? != some '-' && !isEnvar a then
            do return (← applyOpt r c (some a), true)
          else do return (← applyOpt r c none, false)
        | none => do return (← applyOpt r c none, false)
      else do return (← applyOpt r c (some (String.ofList cs)), false)

/-- Process `--name[=value]` (`body` = the characters after `--`). -/
def longOpt (r : Raw) (next : Option String) (body : List Char) : Except String (Raw × Bool) :=
  let name := body.takeWhile (· != '=')
  let hasArg := body.contains '='
  let value := String.ofList ((body.dropWhile (· != '=')).drop 1)
  let visible := longOpts.filter (fun o => !(r.sudoedit && o.sudoOnly))
  let cands :=
    match visible.find? (fun o => o.name.toList == name) with
    | some o => [o]
    | none => visible.filter (fun o => name.isPrefixOf o.name.toList)
  let full := "--" ++ String.ofList body
  match cands with
  | [] => .error (usageErr r s!"unrecognized option '{full}'")
  | [o] =>
    match o.spec with
    | .no =>
      if hasArg then .error (usageErr r s!"option '--{o.name}' doesn't allow an argument")
      else do return (← applyOpt r o.key none, false)
    | .opt => do return (← applyOpt r o.key (if hasArg then some value else none), false)
    | .req =>
      if hasArg then do return (← applyOpt r o.key (some value), false)
      else match next with
        | some a => do return (← applyOpt r o.key (some a), true)
        | none => .error (usageErr r s!"option '--{o.name}' requires an argument")
  | os =>
    .error (usageErr r (s!"option '{full}' is ambiguous; possibilities:" ++
      String.join (os.map fun o => s!" '--{o.name}'")))

/-- getopt_long loop with sudo's `VAR=value` interleaving. Returns the final state and
the operands. -/
def scan : List String → Raw → Except String (Raw × List String)
  | [], r => .ok (r, [])
  | a :: rest, r =>
    match a.toList with
    | ['-', '-'] => .ok (r, rest)
    | '-' :: '-' :: body =>
      match longOpt r rest.head? body with
      | .error e => .error e
      | .ok (r', true) => scan rest.tail r'
      | .ok (r', false) => scan rest r'
    | '-' :: c :: cs =>
      match shortCluster r rest.head? (a.toList == ['-', 'h']) (c :: cs) with
      | .error e => .error e
      | .ok (r', true) => scan rest.tail r'
      | .ok (r', false) => scan rest r'
    | l =>
      if isEnvarL l then scan rest { r with envVars := r.envVars ++ [splitEnvar a] }
      else .ok (r, a :: rest)
termination_by args => args.length
decreasing_by all_goals (simp only [List.length_tail, List.length_cons]; omega)

/-! ## Validation (the tail of sudo's `parse_args`) -/

/-- The mode sudo settles on (`-k` alone becomes `resetTimestamp`). -/
def Raw.effMode (r : Raw) (ops : List String) : Mode :=
  match r.mode with
  | some m => m
  | none => if r.ignoreTicket && ops.isEmpty && !(r.shell || r.login) then .resetTimestamp else .run

/-- sudo's `(flags & valid_flags) != flags` check. Flags: `-b -E -H -i -n -P -s`
and the second `-l`. -/
def Raw.flagsValid (r : Raw) (m : Mode) : Bool :=
  match m with
  | .run => true
  | .edit | .validate => !(r.background || r.preserveAll || r.resetHome || r.login ||
      r.preserveGroups || r.shell)
  | .list => !(r.background || r.preserveAll || r.resetHome || r.login ||
      r.preserveGroups || r.shell)
  | _ => !(r.background || r.preserveAll || r.resetHome || r.login || r.nonInteractive ||
      r.preserveGroups || r.shell || r.lcount > 1)

/-- sudo's post-scan checks, in order: (violated?, error text). -/
def Raw.rules (r : Raw) (ops : List String) : List (Bool × String) :=
  let m := r.effMode ops
  let usage := usageFor r.progname
  let editEnv := !(r.envVars.isEmpty && r.preserveVars.isEmpty)
  [ (r.login && r.shell, usageErr r "you may not specify both the -i and -s options"),
    (r.login && r.preserveAll, usageErr r "you may not specify both the -i and -E options"),
    (m == .edit && r.preserveAll && editEnv,
      usageErr r ("the -E option is not valid in edit mode\n" ++ r.progname ++
        ": you may not specify environment variables in edit mode")),
    (m == .edit && r.preserveAll, usageErr r "the -E option is not valid in edit mode"),
    (m == .edit && editEnv, usageErr r "you may not specify environment variables in edit mode"),
    (!r.flagsValid m, usage),
    ((r.user.isSome || r.group.isSome) &&
      !(m == .edit || m == .run || m == .validate || (m == .list && !ops.isEmpty)), usage),
    (r.otherUser.isSome && m != .list,
      usageErr r "the -U option may only be used with the -l option"),
    (r.stdin && r.askpass, usageErr r "the -A and -S options may not be used together"),
    ((ops.isEmpty && m == .edit) || (!ops.isEmpty && !(m == .run || m == .edit || m == .list)),
      usage),
    -- sudo would set "implied shell" here and let `shell_noargs` decide; we always
    -- require -s/-i or a command (sudo's behaviour without `shell_noargs`)
    (ops.isEmpty && m == .run && !(r.shell || r.login), usage) ]

/-- First validation error, if any. -/
def Raw.check (r : Raw) (ops : List String) : Option String :=
  ((r.rules ops).find? (·.1)).map (·.2)

def Raw.build (r : Raw) (ops : List String) : Options :=
  let m := r.effMode ops
  { mode := m
    user := r.user
    group := r.group
    otherUser := r.otherUser
    login := r.login
    shell := r.shell
    preserveEnv := if r.preserveAll then .all
      else if r.preserveVars.isEmpty then .none else .vars r.preserveVars
    setHome := r.resetHome
    nonInteractive := r.nonInteractive
    stdin := r.stdin
    prompt := r.prompt
    background := r.background
    resetTimestamp := r.ignoreTicket && m != .resetTimestamp && m != .removeTimestamp
    chdir := r.chdir
    listVerbose := r.lcount
    preserveGroups := r.preserveGroups
    bell := r.bell
    closeFrom := r.closeFrom
    askpass := r.askpass
    noUpdate := r.noUpdate
    envVars := r.envVars
    command := ops }

def finish (r : Raw) (ops : List String) : Except String Options :=
  match r.check ops with
  | some e => .error e
  | none => .ok (r.build ops)

/-- Parse sudo's command line. `progname` is the basename of `argv[0]`, `args` are
`argv[1..]`. -/
def parseArgs (progname : String) (args : List String) : Except String Options :=
  match scan args (Raw.init progname) with
  | .error e => .error e
  | .ok (r, ops) => finish r ops

/-! ## Shell mode (`-s` / `-i`) -/

/-- Characters sudo leaves unescaped when building `shell -c "..."`. -/
def shellSafe (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '-' || c == '$'

/-- Backslash-escape every character that is not `shellSafe`. -/
def escapeChars : List Char → List Char
  | [] => []
  | c :: cs => if shellSafe c then c :: escapeChars cs else '\\' :: c :: escapeChars cs

/-- Escape every word and join them with single spaces. -/
def escapeJoin : List String → List Char
  | [] => []
  | [w] => escapeChars w.toList
  | w :: ws => escapeChars w.toList ++ ' ' :: escapeJoin ws

/-- The `-c` argument sudo builds from the command words. -/
def shellEscape (command : List String) : String := String.ofList (escapeJoin command)

structure ShellCmd where
  /-- path to execute -/
  path : String
  /-- full argv including argv[0] -/
  argv : List String
  deriving Repr, DecidableEq, Inhabited

/-- The command executed for `-s` (`login = false`) or `-i` (`login = true`).
`shell` is the shell path (`-s`: the invoking user's `$SHELL` or passwd shell;
`-i`: the target user's passwd shell). -/
def shellCommand (shell : String) (login : Bool) (command : List String) : ShellCmd :=
  let argv0 := if login then "-" ++ basename shell else shell
  { path := shell
    argv := if command.isEmpty then [argv0] else [argv0, "-c", shellEscape command] }

end LeanSudo.Cli
