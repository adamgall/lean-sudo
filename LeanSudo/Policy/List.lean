import LeanSudo.Policy.Defaults
import LeanSudo.Sss
import LeanSudo.Cli

/-!
# `sudo -l` rendering

`listPrivileges` renders sudo 1.9.17p2's short and verbose listing formats:

```
Matching Defaults entries for alice on host:
    env_reset, mail_badpass, secure_path=/usr/local/sbin\:/usr/bin

Runas and Command-specific defaults for alice:
    Defaults>root !set_logname

User alice may run the following commands on host:
    (ALL : ALL) ALL
    (root) NOPASSWD: /usr/bin/ls, /usr/bin/cat
```

* "Matching Defaults entries": global, matching `Defaults@host` and matching
  `Defaults:user` entries, in file order; omitted when empty.
* "Runas and Command-specific defaults": every `Defaults>…` then every `Defaults!…`
  entry (sudo prints them without matching); omitted when empty.
* Privileges: every command spec of every user spec whose user list matches `user`
  and whose host list matches `host`. Inherited run-as specs join on a line; an
  explicit run-as spec starts a new line even if its value is unchanged. Aliases
  expand with negation composition. Verbose entries retain source filenames.
* No privileges ⇒ only `User <u> is not allowed to run sudo on <h>.`
* Output folding shares `Cli.wrapListing` with help text and follows `sudo_lbuf_print`,
  using separate Defaults and privilege indents; zero columns means unwrapped output.

The result ends with a newline.
-/

namespace LeanSudo.Policy

open LeanSudo.Sudoers

/-- Backslash-escape the given characters. -/
def escapeChars (special : List Char) (s : String) : String :=
  String.ofList (s.toList.flatMap fun c => if special.contains c then ['\\', c] else [c])

def renderUserAtom : UserAtom → String
  | .all => "ALL"
  | .name n => n
  | .id n => s!"#{n}"
  | .group n => s!"%{n}"
  | .gid n => s!"%#{n}"
  | .nonunixGroup n => s!"%:{n}"
  | .nonunixGid n => s!"%:#{n}"
  | .netgroup n => s!"+{n}"
  | .myself => ""
  | .alias n => n

def renderIp : IpAddr → String
  | .v4 bs => ".".intercalate (bs.map (toString ·.toNat))
  | .v6 bs =>
    let hex (n : Nat) : String := String.ofList (Nat.toDigits 16 n)
    let rec words : List UInt8 → List String
      | a :: b :: rest => hex (a.toNat * 256 + b.toNat) :: words rest
      | _ => []
    ":".intercalate (words bs)

def renderHostAtom : HostAtom → String
  | .all => "ALL"
  | .name n => n
  | .netgroup n => s!"+{n}"
  | .network a m => renderIp a ++ "/" ++ renderIp m
  | .alias n => n

def renderArgs : CmndArgs → String
  | .any => ""
  | .none => " \"\""
  | .pattern q => " " ++ escapeChars [',', ':', '=', '#'] q
  | .regex re => " " ++ re

def renderDigestAlgo : DigestAlgo → String
  | .sha224 => "sha224" | .sha256 => "sha256" | .sha384 => "sha384" | .sha512 => "sha512"

def renderDigest (d : Digest) : String :=
  let hex2 (b : UInt8) : String :=
    let s := String.ofList (Nat.toDigits 16 b.toNat)
    if s.length < 2 then "0" ++ s else s
  renderDigestAlgo d.algo ++ ":" ++
    (if d.spelling.isEmpty then String.join (d.bytes.map hex2) else d.spelling)

def renderCmndAtom : CmndAtom → String
  | .all => "ALL"
  | .alias n => n
  | .command p a => escapeChars [':', ',', '=', ' ', '\t', '#'] p ++ renderArgs a
  | .commandRegex re a => re ++ renderArgs a
  | .sudoedit a => "sudoedit" ++ renderArgs a
  | .list => "list"
  | .digest ds c => ", ".intercalate (ds.map renderDigest) ++ " " ++ renderCmndAtom c

def renderMember {α : Type} (f : α → String) (m : Member α) : String :=
  (if m.negated then "!" else "") ++ f m.atom

def renderMembers {α : Type} (f : α → String) (l : List (Member α)) : String :=
  ", ".intercalate (l.map (renderMember f))

private def renderCommandMember (m : Member CmndAtom) : String :=
  go m.atom
where
  go : CmndAtom → String
    | .digest ds c => ", ".intercalate (ds.map renderDigest) ++ " " ++ go c
    | c => (if m.negated then "!" else "") ++ renderCmndAtom c

private def renderUserMember (user : String) (m : Member UserAtom) : String :=
  let neg := if m.negated then "!" else ""
  let word (s : String) :=
    if s.toList.any (fun c => c == ' ' || c == '\t') then neg ++ "\"" ++ escapeChars ['"'] s ++ "\""
    else if s.startsWith "#" && (s.drop 1).toString.toList.all Char.isDigit then neg ++ s
    else neg ++ escapeChars [':', ',', '=', '#', '"'] s
  let group (marker name : String) :=
    if name.toList.any (fun c => c == ' ' || c == '\t') then word (marker ++ name)
    else marker ++ word name
  match m.atom with
  | .group name => group "%" name
  | .gid gid => group "%" s!"#{gid}"
  | .nonunixGroup name => group "%:" name
  | .nonunixGid gid => group "%:" s!"#{gid}"
  | .myself => neg ++ user
  | a => word (renderUserAtom a)

/-- sudo quotes values containing blanks and escapes sudoers metacharacters otherwise. -/
def renderDefaultsValue (v : String) : String :=
  if v.toList.any (fun c => c == ' ' || c == '\t') then "\"" ++ escapeChars ['"'] v ++ "\""
  else escapeChars [':', ',', '=', '#', '"'] v

def renderSetting (d : DefaultsSetting) : String :=
  match d.op with
  | .flag _ => opText d.op ++ d.name
  | .assign v | .add v | .remove v => d.name ++ opText d.op ++ renderDefaultsValue v

/-- Expand aliases without losing the polarity inherited from enclosing aliases. -/
def expandMembers {α : Type} (aliasName : α → Option String)
    (defs : List (String × List (Member α))) : Nat → Bool → List (Member α) → List (Member α)
  | 0, neg, ms => ms.map fun m => { m with negated := m.negated != neg }
  | fuel + 1, neg, ms => ms.flatMap fun m =>
    let flipped := m.negated != neg
    match (aliasName m.atom).bind (lookupAlias defs) with
    | some children => expandMembers aliasName defs fuel flipped children
    | none => [{ m with negated := flipped }]

theorem expandMembers_zero_negation {α : Type} (name : α → Option String)
    (defs : List (String × List (Member α))) (m : Member α) :
    expandMembers name defs 0 true [m] = [{ m with negated := !m.negated }] := by
  cases m with
  | mk neg atom => cases neg <;> rfl

private def expandedUsers (al : Aliases) (user : String) (ms : List (Member UserAtom)) : String :=
  ", ".intercalate ((expandMembers UserAtom.aliasName al.runas al.fuel false ms).map
    (renderUserMember user))

private def expandedCommands (al : Aliases) (separator : String) (m : Member CmndAtom) : String :=
  separator.intercalate ((expandMembers CmndAtom.aliasName al.cmnd al.fuel false [m]).map
    renderCommandMember)

private def runasUsers (al : Aliases) (st : Settings) (user : String) : Option RunasSpec → String
  | none | some ⟨none, none⟩ => st.runasDefault
  | some ⟨some us, _⟩ => expandedUsers al user us
  | some ⟨none, some _⟩ => user

def renderRunas (st : Settings) (rs : Option RunasSpec) (al : Aliases := {})
    (user : String := "") : String :=
  let groups := (rs.bind (·.groups)).map fun gs => " : " ++ expandedUsers al user gs
  "(" ++ runasUsers al st user rs ++ groups.getD "" ++ ")"

/-- UTC generalized time, the format sudo uses when displaying time restrictions. -/
def renderGeneralizedTime (seconds : Nat) : String :=
  let days := seconds / 86400
  let leap (y : Nat) := y % 4 == 0 && (y % 100 != 0 || y % 400 == 0)
  let start := 1970 + days / 146097 * 400
  let (year, day) := (List.range 400).foldl (fun (y, d) _ =>
    let size := if leap y then 366 else 365
    if d ≥ size then (y + 1, d - size) else (y, d)) (start, days % 146097)
  let months := [31, if leap year then 29 else 28, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31]
  let (month, day, _) := months.foldl (fun (m, d, done_) size =>
    if done_ || d < size then (m, d, true) else (m + 1, d - size, false)) (1, day, false)
  let pad (n width : Nat) :=
    let text := toString n
    String.ofList (List.replicate (width - text.length) '0') ++ text
  pad year 4 ++ pad month 2 ++ pad (day + 1) 2 ++
    pad (seconds / 3600 % 24) 2 ++ pad (seconds / 60 % 60) 2 ++ pad (seconds % 60) 2 ++ "Z"

/-- Changed options precede tags, in fmtsudoers.c's order. -/
def renderOptsTags (prev : Option CmndSpec) (cs : CmndSpec) : String :=
  let changed {β : Type} [BEq β] (get : CmndSpec → Option β) : Option β :=
    match get cs with
    | some v => if prev.map get == some (some v) then none else some v
    | none => none
  let written {β : Type} [BEq β] (name : String) (get : CmndSpec → Option β) : Option β :=
    if cs.optionsExplicit.contains name then get cs else changed get
  let option (label : String) (v : Option String) := (v.map fun s => label ++ "=" ++ s ++ " ").getD ""
  let tag (yes no : String) (v : Option Bool) := (v.map fun b => (if b then yes else no) ++ ": ").getD ""
  option "PRIVS" ((written "PRIVS" (·.options.privs)).map fun s => "\"" ++ s ++ "\"") ++
  option "LIMITPRIVS" ((written "LIMITPRIVS" (·.options.limitprivs)).map fun s => "\"" ++ s ++ "\"") ++
  option "ROLE" (written "ROLE" (·.options.role)) ++
  option "TYPE" (written "TYPE" (·.options.type)) ++
  option "APPARMOR_PROFILE" (written "APPARMOR_PROFILE" (·.options.apparmorProfile)) ++
  option "CHROOT" (written "CHROOT" (·.options.chroot)) ++
  option "CWD" ((written "CWD" (·.options.cwd)).map (·.getD "*")) ++
  option "TIMEOUT" (((changed (·.options.timeout)).filter (· > 0)).map toString) ++
  option "NOTBEFORE" ((changed (·.options.notBefore)).map renderGeneralizedTime) ++
  option "NOTAFTER" ((changed (·.options.notAfter)).map renderGeneralizedTime) ++
  tag "SETENV" "NOSETENV" (changed (·.tags.setenv)) ++
  tag "INTERCEPT" "NOINTERCEPT" (changed (·.tags.intercept)) ++
  tag "NOEXEC" "EXEC" (changed (·.tags.noexec)) ++
  tag "PASSWD" "NOPASSWD" (changed (·.tags.passwd)) ++
  tag "LOG_INPUT" "NOLOG_INPUT" (changed (·.tags.logInput)) ++
  tag "LOG_OUTPUT" "NOLOG_OUTPUT" (changed (·.tags.logOutput)) ++
  tag "MAIL" "NOMAIL" (changed (·.tags.mail)) ++
  tag "FOLLOW" "NOFOLLOW" (changed (·.tags.follow))

def renderCmndSpecs (st : Settings) (cmnds : List CmndSpec) (al : Aliases := {})
    (user : String := "") : List String :=
  go none "" cmnds
where
  go : Option CmndSpec → String → List CmndSpec → List String
    | none, _, [] => []
    | some _, cur, [] => [cur]
    | prev, cur, cs :: rest =>
      let same := prev.any fun p => !cs.runasExplicit && p.runas == cs.runas
      let body := renderOptsTags (if same then prev else none) cs ++ expandedCommands al ", " cs.cmnd
      if same then go (some cs) (cur ++ ", " ++ body) rest
      else
        let line := "    " ++ renderRunas st cs.runas al user ++ " " ++ body
        (if prev.isSome then [cur] else []) ++ go (some cs) line rest

private def longHeader (al : Aliases) (st : Settings) (user file : String) (cs : CmndSpec) : String :=
  let option (name : String) (v : Option Bool) :=
    v.map fun b => (if b then "" else "!") ++ name
  let options := if cs.ldapRole.isSome then cs.ldapOptions.map (renderSetting ∘ Sss.parseOption)
    else [option "setenv" cs.tags.setenv, option "noexec" cs.tags.noexec,
      option "intercept" cs.tags.intercept, option "authenticate" cs.tags.passwd,
      option "log_input" cs.tags.logInput, option "log_output" cs.tags.logOutput].filterMap id
  let field (name : String) (v : Option String) :=
    (v.map fun text => "    " ++ name ++ ": " ++ text ++ "\n").getD ""
  (cs.ldapRole.map (fun name => s!"LDAP Role: {name}\n") |>.getD s!"Sudoers entry: {file}\n") ++
  s!"    RunAsUsers: {runasUsers al st user cs.runas}\n" ++
  field "RunAsGroups" ((cs.runas.bind (·.groups)).map (expandedUsers al user)) ++
  (if options.isEmpty then "" else "    Options: " ++ ", ".intercalate options ++ "\n") ++
  field "ApparmorProfile" cs.options.apparmorProfile ++
  field "Privs" cs.options.privs ++ field "Limitprivs" cs.options.limitprivs ++
  field "Role" cs.options.role ++ field "Type" cs.options.type ++
  field "Chroot" cs.options.chroot ++ field "Cwd" (cs.options.cwd.map (·.getD "*")) ++
  field "Timeout" ((cs.options.timeout.filter (· > 0)).map toString) ++
  field "NotBefore" (cs.options.notBefore.map renderGeneralizedTime) ++
  field "NotAfter" (cs.options.notAfter.map renderGeneralizedTime) ++ "    Commands:\n"

def renderLongSpecs (al : Aliases) (st : Settings) (user file : String)
    (cmnds : List CmndSpec) : String :=
  (cmnds.foldl (fun (prev, output) cs =>
    let same := prev.any fun p => !cs.runasExplicit && p.runas == cs.runas &&
      p.tags == cs.tags && p.options == cs.options
    let header := if same then "" else "\n" ++ longHeader al st user file cs
    (some cs, output ++ header ++ "\t" ++ expandedCommands al "\n\t" cs.cmnd ++ "\n"))
    (none, "")).2

def notAllowedMessage (user host : String) : String :=
  s!"User {user} is not allowed to run sudo on {host}."

private def sources (s : Sudoers) (located : List Located) : List Located :=
  if located.isEmpty then
    s.map fun e => { file := "/etc/sudoers", line := 1, entry := e }
  else located

/-- Omit specs whose local bounds lack system-zone facts, rather than rendering
an unresolved civil timestamp as UTC. Matching and display share the resolver. -/
private def displaySpec (localTimeBounds : List (Nat × Nat)) (cs : CmndSpec) :
    Option CmndSpec := do
  let resolve (localTime : Bool) : Option Nat → Option (Option Nat)
    | none => some none
    | some n => (resolveTimeBound localTimeBounds localTime n).map some
  let notBefore ← resolve cs.options.notBeforeLocal cs.options.notBefore
  let notAfter ← resolve cs.options.notAfterLocal cs.options.notAfter
  pure { cs with options := { cs.options with
    notBefore, notAfter, notBeforeLocal := false, notAfterLocal := false } }

/-- Short or verbose privileges. Locations preserve the source filename for `-ll`. -/
def listPrivileges (s : Sudoers) (st : Settings) (user : Principal) (host : String)
    (verbose : Bool := false) (located : List Located := [])
    (facts : Option Request := none) (columns : Nat := 0) : String :=
  let al := aliasesOf s
  let f := al.fuel
  let ds := defaultsOf s
  let matching := ds.flatMap fun
    | (.global, ss) => ss
    | (.host hs, ss) => if hostListOk al f host hs st facts then ss else []
    | (.user us, ss) => if userListOk al f user us st facts then ss else []
    | _ => []
  let runasBound := ds.filterMap fun
    | (.runas rs, ss) => some s!"    Defaults>{expandedUsers al user.name rs} {", ".intercalate (ss.map renderSetting)}"
    | _ => none
  let commandBound := ds.filterMap fun
    | (.cmnd cs, ss) => some s!"    Defaults!{", ".intercalate (cs.map (expandedCommands al ", "))} {", ".intercalate (ss.map renderSetting)}"
    | _ => none
  -- display_bound_defaults_by_type does not insert a newline between the two types.
  let bound := "\n".intercalate runasBound ++ "\n".intercalate commandBound
  let privs := (sources s located).flatMap fun l =>
    match l.entry with
    | .userSpec us =>
      if userListOk al f user us.users st facts then
        us.entries.filterMap fun hc =>
          if hostListOk al f host hc.hosts st facts then
            let cmnds := hc.cmnds.filterMap (displaySpec ((facts.map (·.localTimeBounds)).getD []))
            if cmnds.isEmpty then none else
              some (if verbose then renderLongSpecs al st user.name l.file cmnds
                else String.join ((renderCmndSpecs st cmnds al user.name).map (· ++ "\n")))
          else none
      else []
    | _ => []
  if privs.isEmpty then Cli.wrapListing (notAllowedMessage user.name host ++ "\n") columns 8
  else
    let defsSec := if matching.isEmpty then "" else
      s!"Matching Defaults entries for {user.name} on {host}:\n    " ++
        ", ".intercalate (matching.map renderSetting) ++ "\n\n"
    let boundSec := if bound.isEmpty then "" else
      s!"Runas and Command-specific defaults for {user.name}:\n" ++ bound ++ "\n\n"
    Cli.wrapListing (defsSec ++ boundSec) columns 4 ++
      Cli.wrapListing
        (s!"User {user.name} may run the following commands on {host}:\n" ++ String.join privs)
        columns 8

/-- Display the exact last matching command specification for `sudo -ll command`. -/
def listCommand (s : Sudoers) (st : Settings) (r : Request) (located : List Located := [])
    (verbose : Bool := false) : String :=
  let al := aliasesOf s
  let matchingSpecs := (sources s located).flatMap fun l =>
    match l.entry with
    | .userSpec us => (usCandidates al al.fuel st r us).map (l.file, ·)
    | _ => []
  match matchingSpecs.getLast? with
  | some (file, candidate) =>
    if !candidate.allow then "" else
    match displaySpec r.localTimeBounds candidate.spec with
    | none => ""
    | some displayed =>
      let cmd := if r.command == .validate then "list" else r.command.text
      (if verbose then longHeader al st r.user.name file displayed ++ "\t" ++
        expandedCommands al "\n\t" displayed.cmnd ++ "\n    Matched: " else "") ++ cmd ++ "\n"
  | none => ""

end LeanSudo.Policy
