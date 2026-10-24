import LeanSudo.Sudoers.Parser

/-! Compile-time tests for `LeanSudo.Sudoers.parse`. -/

namespace Tests.Parser

open LeanSudo.Sudoers

def entriesOf (t : String) : Option (List Entry) :=
  match parse "t" t with
  | .ok ls => some (ls.map (·.entry))
  | .error _ => none

def linesOf (t : String) : Option (List Nat) :=
  match parse "t" t with
  | .ok ls => some (ls.map (·.line))
  | .error _ => none

def errOf (t : String) : Option ParseError :=
  match parse "t" t with
  | .ok _ => none
  | .error e => some e

/-- Parsing fails and the message mentions `sub`. -/
def failsWith (t sub : String) : Bool :=
  match parse "t" t with
  | .ok _ => false
  | .error e => e.msg.contains sub

/-- Parsing fails (any reason). -/
def fails (t : String) : Bool := (errOf t).isSome

def pos (a : α) : Member α := ⟨false, a⟩
def neg (a : α) : Member α := ⟨true, a⟩

def cmd (p : String) (args : CmndArgs := .any) : CmndAtom := .command p args

def runas (us : Option (List (Member UserAtom))) (gs : Option (List (Member UserAtom)) := none) :
    Option RunasSpec :=
  some { users := us, groups := gs }

def spec (c : Member CmndAtom) (r : Option RunasSpec := none) (t : Tags := {})
    (o : CmndOptions := {}) : CmndSpec :=
  { runas := r, options := o, tags := t, cmnd := c }

def uspec (us : List (Member UserAtom)) (hs : List (Member HostAtom)) (cs : List CmndSpec) :
    Entry :=
  .userSpec { users := us, entries := [{ hosts := hs, cmnds := cs }] }

def dflt (name : String) (op : DefaultsOp) (scope : DefaultsScope := .global) : Entry :=
  .defaults scope [{ name, op }]

/-! ## Ubuntu's default /etc/sudoers -/

def ubuntu : String := include_str "../fixtures/sudoers/ubuntu"

def allAll : Option RunasSpec := runas (some [pos .all]) (some [pos .all])

#guard entriesOf ubuntu == some [
  dflt "env_reset" (.flag true),
  dflt "mail_badpass" (.flag true),
  dflt "secure_path" (.assign "/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/snap/bin"),
  dflt "use_pty" (.flag true),
  uspec [pos (.name "root")] [pos .all] [spec (pos .all) allAll],
  uspec [pos (.group "admin")] [pos .all] [spec (pos .all) (runas (some [pos .all]))],
  uspec [pos (.group "sudo")] [pos .all] [spec (pos .all) allAll],
  .includeDir "/etc/sudoers.d"]

#guard linesOf ubuntu == some [9, 10, 11, 15, 47, 50, 53, 57]

#guard (parse "/etc/sudoers" ubuntu).toOption.map (·.all (·.file == "/etc/sudoers")) == some true

/-! ## A larger file: aliases, scoped Defaults, inheritance, multi-host specs -/

def complex : String := include_str "../fixtures/sudoers/complex"

def opWheel : Option RunasSpec := runas (some [pos (.alias "OP")]) (some [pos (.name "wheel")])
def rootRunas : Option RunasSpec := runas (some [pos (.name "root")])

#guard entriesOf complex == some [
  .userAlias "ADMINS" [pos (.name "alice"), pos (.name "bob"), pos (.group "wheel")],
  .userAlias "OPS" [pos (.name "carol")],
  .runasAlias "OP" [pos (.name "root"), pos (.name "operator")],
  .hostAlias "SERVERS" [pos (.name "web1"), pos (.name "db*.example.com"),
    neg (.name "db9.example.com")],
  .cmndAlias "SHELLS" [pos (cmd "/bin/sh"), pos (cmd "/bin/bash"), pos (cmd "/usr/bin/zsh")],
  .cmndAlias "PRINT" [pos (cmd "/usr/bin/lp" .none)],
  .defaults .global [{ name := "env_keep", op := .add "A B" },
    { name := "lecture", op := .flag false }],
  dflt "authenticate" (.flag false) (.user [pos (.name "alice")]),
  dflt "set_logname" (.flag false) (.runas [pos (.name "root")]),
  dflt "use_pty" (.flag true) (.cmnd [pos (cmd "/bin/ls")]),
  .defaults (.host [pos (.alias "SERVERS")]) [{ name := "log_output", op := .flag true },
    { name := "passprompt", op := .assign "Pw \"x\": " }],
  uspec [pos (.name "alice")] [pos .all] [
    spec (pos (cmd "/bin/ls")) rootRunas { passwd := some false },
    spec (pos (cmd "/bin/cat")) rootRunas { passwd := some false },
    spec (pos (cmd "/bin/sh")) rootRunas { passwd := some true }],
  .userSpec { users := [pos (.alias "ADMINS")], entries := [
    { hosts := [pos (.alias "SERVERS")], cmnds := [
      spec (pos .all) opWheel { setenv := some true },
      spec (neg (.alias "SHELLS")) opWheel { setenv := some true }] },
    { hosts := [pos (.name "db1")], cmnds := [
      spec (pos (cmd "/usr/bin/vi" (.pattern "/etc/hosts"))) (runas none (some [pos (.name "adm")]))
        {} { cwd := some (some "/tmp") }] }] },
  uspec [pos (.gid 27), pos (.id 1000)] [pos .all] [
    spec (pos .all), spec (neg (cmd "/usr/bin/su")), spec (pos (cmd "/usr/bin/id"))],
  uspec [pos (.name "dave")] [pos .all] [
    spec (pos (.sudoedit (.pattern "/etc/motd"))),
    spec (pos (cmd "/usr/bin/printf" (.pattern "a,b:c d")))]]

#guard linesOf complex == some [2, 2, 3, 4, 5, 7, 9, 10, 11, 12, 13, 16, 17, 18, 19]

/-! ## Individual constructs -/

-- inheritance: run-as and tags carry over; a later tag of the same kind overrides
#guard entriesOf "alice ALL = (root) NOPASSWD: /bin/ls, /bin/cat, PASSWD: /bin/sh" == some [
  uspec [pos (.name "alice")] [pos .all] [
    spec (pos (cmd "/bin/ls")) rootRunas { passwd := some false },
    spec (pos (cmd "/bin/cat")) rootRunas { passwd := some false },
    spec (pos (cmd "/bin/sh")) rootRunas { passwd := some true }]]

-- a new run-as spec replaces the whole run-as; tags of other kinds are kept
#guard entriesOf "a ALL = (root:wheel) NOPASSWD: /a, (bob) SETENV: /b, /c" == some [
  uspec [pos (.name "a")] [pos .all] [
    spec (pos (cmd "/a")) (runas (some [pos (.name "root")]) (some [pos (.name "wheel")]))
      { passwd := some false },
    spec (pos (cmd "/b")) (runas (some [pos (.name "bob")])) { passwd := some false, setenv := some true },
    spec (pos (cmd "/c")) (runas (some [pos (.name "bob")])) { passwd := some false, setenv := some true }]]

-- inheritance resets at each `: Host_List =`
#guard entriesOf "a h1 = (root) NOPASSWD: /a : h2 = /b" == some [
  .userSpec { users := [pos (.name "a")], entries := [
    { hosts := [pos (.name "h1")], cmnds := [spec (pos (cmd "/a")) rootRunas { passwd := some false }] },
    { hosts := [pos (.name "h2")], cmnds := [spec (pos (cmd "/b"))] }] }]

-- CWD options carry over like tags; CWD=* lets the user choose
#guard entriesOf "a ALL = CWD=/tmp /a, /b, CWD=* /c" == some [
  uspec [pos (.name "a")] [pos .all] [
    spec (pos (cmd "/a")) none {} { cwd := some (some "/tmp") },
    spec (pos (cmd "/b")) none {} { cwd := some (some "/tmp") },
    spec (pos (cmd "/c")) none {} { cwd := some none }]]

-- negation parity
#guard entriesOf "!!alice, !bob ALL = ALL, !/usr/bin/su, !!/bin/x, ! ! ! SHELLS" == some [
  uspec [pos (.name "alice"), neg (.name "bob")] [pos .all] [
    spec (pos .all), spec (neg (cmd "/usr/bin/su")), spec (pos (cmd "/bin/x")),
    spec (neg (.alias "SHELLS"))]]

-- `#uid`, `%#gid` (also at the start of a line: not a comment), `%group`, quoted names
#guard entriesOf "#1000 ALL = (#0 : %#27) ALL" == some [
  uspec [pos (.id 1000)] [pos .all] [spec (pos .all) (runas (some [pos (.id 0)]) (some [pos (.gid 27)]))]]
#guard entriesOf "%#27, %\"domain users\", \"bob smith\" ALL = ALL" == some [
  uspec [pos (.gid 27), pos (.group "domain users"), pos (.name "bob smith")] [pos .all] [spec (pos .all)]]
#guard entriesOf "j\\ doe, user.name-x$, a@b ALL = ALL" == some [
  uspec [pos (.name "j doe"), pos (.name "user.name-x$"), pos (.name "a@b")] [pos .all] [spec (pos .all)]]

-- empty run-as specs
#guard entriesOf "a ALL = () /a, (:) /b, (: wheel) /c" == some [
  uspec [pos (.name "a")] [pos .all] [
    spec (pos (cmd "/a")) (runas none), spec (pos (cmd "/b")) (runas none),
    spec (pos (cmd "/c")) (runas none (some [pos (.name "wheel")]))]]

-- dropped tags have no effect
#guard entriesOf "a ALL = EXEC: NOINTERCEPT: MAIL: NOMAIL: FOLLOW: NOFOLLOW: LOG_INPUT: NOLOG_INPUT: LOG_OUTPUT: NOLOG_OUTPUT: NOSETENV: /a" ==
  some [uspec [pos (.name "a")] [pos .all] [spec (pos (cmd "/a")) none { setenv := some false }]]

-- host wildcards and aliases
#guard entriesOf "a web*, db[0-9].lan, !OLD, ALL = ALL" == some [
  uspec [pos (.name "a")] [pos (.name "web*"), pos (.name "db[0-9].lan"), neg (.alias "OLD"), pos .all]
    [spec (pos .all)]]

-- command arguments: escapes, glob escapes kept, whitespace collapsed, `""`
#guard entriesOf "a ALL = /bin/echo a\\,b\\:c\\=d\\\\e   f\\ g, /bin/ls \\*, /bin/true \"\"" == some [
  uspec [pos (.name "a")] [pos .all] [
    spec (pos (cmd "/bin/echo" (.pattern "a,b:c=d\\e f g"))),
    spec (pos (cmd "/bin/ls" (.pattern "\\*"))),
    spec (pos (cmd "/bin/true" .none))]]
#guard entriesOf "a ALL = /usr/bin/*, /usr/sbin/, /bin/kill -[0-9]* *" == some [
  uspec [pos (.name "a")] [pos .all] [
    spec (pos (cmd "/usr/bin/*")), spec (pos (cmd "/usr/sbin/")),
    spec (pos (cmd "/bin/kill" (.pattern "-[0-9]* *")))]]
-- `#` ends command arguments and starts a comment
#guard entriesOf "a ALL = /bin/echo hi # comment" == some [
  uspec [pos (.name "a")] [pos .all] [spec (pos (cmd "/bin/echo" (.pattern "hi")))]]
#guard entriesOf "a ALL = /bin/echo a\\#b" == some [
  uspec [pos (.name "a")] [pos .all] [spec (pos (cmd "/bin/echo" (.pattern "a#b")))]]

-- line continuations; entry line is the first line; comments ending in `\` do not continue
#guard entriesOf "alice ALL = \\\n   /bin/ls \\\n  -l, \\\n /bin/cat\n" == some [
  uspec [pos (.name "alice")] [pos .all] [
    spec (pos (cmd "/bin/ls" (.pattern "-l"))), spec (pos (cmd "/bin/cat"))]]
#guard linesOf "\n# c\n\nalice ALL = \\\n /bin/ls\nbob ALL = ALL" == some [4, 6]
#guard linesOf "# comment \\\nroot ALL = ALL\n" == some [2]
#guard linesOf "root ALL = ALL # comment \\\nbob ALL = ALL\n" == some [1, 2]

-- Defaults forms and values
#guard entriesOf "Defaults env_keep += \"A B\"" == some [dflt "env_keep" (.add "A B")]
#guard entriesOf "Defaults env_keep-=HOME, env_delete=X\\ Y,!!lecture,!!!fqdn" == some [
  .defaults .global [{ name := "env_keep", op := .remove "HOME" },
    { name := "env_delete", op := .assign "X Y" }, { name := "lecture", op := .flag true },
    { name := "fqdn", op := .flag false }]]
#guard entriesOf "Defaults secure_path=/usr/bin:/bin" == some [dflt "secure_path" (.assign "/usr/bin:/bin")]
#guard entriesOf "Defaults passprompt=\"a \\\"q\\\" \\\\ b\"" ==
  some [dflt "passprompt" (.assign "a \"q\" \\ b")]
#guard entriesOf "Defaults:alice !authenticate" ==
  some [dflt "authenticate" (.flag false) (.user [pos (.name "alice")])]
#guard entriesOf "Defaults:alice, %wheel, !bob !authenticate" ==
  some [dflt "authenticate" (.flag false)
    (.user [pos (.name "alice"), pos (.group "wheel"), neg (.name "bob")])]
#guard entriesOf "Defaults>root, OP timestamp_timeout=0" ==
  some [dflt "timestamp_timeout" (.assign "0") (.runas [pos (.name "root"), pos (.alias "OP")])]
#guard entriesOf "Defaults!/bin/ls, PAGERS, sudoedit !use_pty" ==
  some [dflt "use_pty" (.flag false) (.cmnd [pos (cmd "/bin/ls"), pos (.alias "PAGERS"),
    pos (.sudoedit .any)])]
#guard entriesOf "Defaults@host1, web* lecture" ==
  some [dflt "lecture" (.flag true) (.host [pos (.name "host1"), pos (.name "web*")])]
#guard entriesOf "Defaults\tsecure_path = \"/a b\"" == some [dflt "secure_path" (.assign "/a b")]

-- includes
#guard entriesOf "#include /etc/sudoers.local\n@include \"/etc/a b\"\n#includedir /etc/sudoers.d\n@includedir /x\n" ==
  some [.include "/etc/sudoers.local", .include "/etc/a b", .includeDir "/etc/sudoers.d",
    .includeDir "/x"]
#guard entriesOf "#includes are mentioned in comments\n" == some []

-- aliases: multiple definitions per line, Cmd_Alias spelling
#guard entriesOf "Host_Alias A = h1 : B = h2, h3\nCmd_Alias C = /bin/a x, sudoedit" == some [
  .hostAlias "A" [pos (.name "h1")], .hostAlias "B" [pos (.name "h2"), pos (.name "h3")],
  .cmndAlias "C" [pos (cmd "/bin/a" (.pattern "x")), pos (.sudoedit .any)]]

-- empty files
#guard entriesOf "" == some []
#guard entriesOf "\n\n# only comments\n   \n" == some []

/-! ## Fail-closed constructs -/

#guard failsWith "+admins ALL = ALL" "netgroups"
#guard failsWith "alice +servers = ALL" "netgroups"
#guard failsWith "Runas_Alias R = +ops" "netgroups"
#guard failsWith "%:Domain\\ Users ALL = ALL" "non-Unix"
#guard failsWith "%:#100 ALL = ALL" "non-Unix"
#guard failsWith "alice 192.168.1.1 = ALL" "IP addresses"
#guard failsWith "alice 10.0.0.0/8 = ALL" "IP addresses"
#guard failsWith "Host_Alias NET = 10.0.0.0/255.0.0.0" "IP addresses"
#guard failsWith "Defaults@10.1.2.* lecture" "IP addresses"
#guard fails "alice fe80::1 = ALL"
#guard fails "Host_Alias V6 = ::1"
#guard failsWith "alice ALL = sha224:abc /bin/ls" "digest"
#guard failsWith "alice ALL = sha256:abc /bin/ls" "digest"
#guard failsWith "alice ALL = sha384:abc /bin/ls" "digest"
#guard failsWith "Cmnd_Alias D = sha512:abc /bin/ls" "digest"
#guard failsWith "alice ALL = ^/usr/bin/.*$" "regular expressions"
#guard failsWith "alice ALL = /bin/ls ^-[la]+$" "regular expressions"
#guard failsWith "alice ALL = ls" "fully-qualified"
#guard failsWith "alice ALL = bin/ls" "fully-qualified"
#guard failsWith "alice ALL = ~/bin/ls" "fully-qualified"
#guard failsWith "alice ALL = list" "list"
#guard failsWith "alice ALL = NOEXEC: /bin/ls" "NOEXEC"
#guard failsWith "alice ALL = INTERCEPT: /bin/ls" "INTERCEPT"
#guard failsWith "alice ALL = CHROOT=/srv /bin/ls" "CHROOT"
#guard failsWith "alice ALL = TIMEOUT=1h /bin/ls" "TIMEOUT"
#guard failsWith "alice ALL = NOTBEFORE=20260101 /bin/ls" "NOTBEFORE"
#guard failsWith "alice ALL = NOTAFTER=20260101 /bin/ls" "NOTAFTER"
#guard failsWith "alice ALL = ROLE=sysadm_r /bin/ls" "ROLE"
#guard failsWith "alice ALL = TYPE=sysadm_t /bin/ls" "TYPE"
#guard failsWith "alice ALL = APPARMOR_PROFILE=x /bin/ls" "APPARMOR_PROFILE"
#guard failsWith "alice ALL = PRIVS=proc_exec /bin/ls" "PRIVS"
#guard failsWith "alice ALL = LIMITPRIVS=proc_exec /bin/ls" "LIMITPRIVS"
#guard failsWith "alice ALL = CWD=~ /bin/ls" "CWD"
-- options must precede tags (as in sudo's grammar)
#guard fails "alice ALL = NOPASSWD: CWD=/tmp /bin/ls"
-- an unsupported construct after a supported prefix still fails
#guard failsWith "alice ALL = (root) NOPASSWD: /bin/ls, NOEXEC: /bin/cat" "NOEXEC"
#guard failsWith "Defaults !env_keep = \"X\"" "cannot take a value"
#guard failsWith "User_Alias ALL = bob" "reserved"
#guard failsWith "User_Alias admins = bob" "invalid alias name"
#guard failsWith "Defaults passprompt=\"abc" "unterminated"
#guard fails "Defaults"
#guard fails "Defaults passprompt="
#guard fails "alice ALL = (root:) ALL"
#guard fails "alice ALL = ALL extra"
#guard fails "alice ALL"
#guard fails "alice ALL = "
#guard fails "alice ALL = /bin/ls\\q"
#guard fails "#12x ALL = ALL"

/-! ## Error positions and formatting -/

#guard (errOf "root ALL = ALL\nalice ALL = ls\n").map (fun e => (e.line, e.col)) == some (2, 13)
#guard (parse "/etc/sudoers" "alice ALL = NOEXEC: /bin/ls").toOption.isNone
#guard (match parse "/etc/sudoers" "\n\nalice ALL = list" with
  | .error e => e.toString
  | .ok _ => "") ==
  "/etc/sudoers:3:13: syntax error: the \"list\" pseudo-command is not supported"

end Tests.Parser
