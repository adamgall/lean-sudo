import LeanSudo.Policy.Defaults

/-!
# `sudo -l` rendering

`listPrivileges` renders sudo 1.9's short `sudo -l` format:

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
  and whose host list matches `host`. Consecutive specs with the same run-as spec are
  joined with `, ` on one line; options and tags are printed when set and different
  from the previous spec on the line (sudo's `TAG_CHANGED`). A spec without run-as
  is shown as `(<runas_default>)`.
* No privileges ⇒ only `User <u> is not allowed to run sudo on <h>.`

The result ends with a newline. Long lines are not folded (sudo folds at the terminal
width).
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
  | .alias n => n

def renderHostAtom : HostAtom → String
  | .all => "ALL"
  | .name n => n
  | .alias n => n

def renderArgs : CmndArgs → String
  | .any => ""
  | .none => " \"\""
  | .pattern q => " " ++ escapeChars [',', ':', '=', '\\'] q

def renderCmndAtom : CmndAtom → String
  | .all => "ALL"
  | .alias n => n
  | .command p a => p ++ renderArgs a
  | .sudoedit a => "sudoedit" ++ renderArgs a

def renderMember {α : Type} (f : α → String) (m : Member α) : String :=
  (if m.negated then "!" else "") ++ f m.atom

def renderMembers {α : Type} (f : α → String) (l : List (Member α)) : String :=
  ", ".intercalate (l.map (renderMember f))

/-- sudo quotes values containing blanks and escapes sudoers metacharacters otherwise. -/
def renderDefaultsValue (v : String) : String :=
  if v.toList.any (fun c => c == ' ' || c == '\t') then "\"" ++ escapeChars ['"'] v ++ "\""
  else escapeChars [':', '\\', ',', '=', '#', '"'] v

def renderSetting (d : DefaultsSetting) : String :=
  match d.op with
  | .flag true => d.name
  | .flag false => "!" ++ d.name
  | .assign v => d.name ++ "=" ++ renderDefaultsValue v
  | .add v => d.name ++ "+=" ++ renderDefaultsValue v
  | .remove v => d.name ++ "-=" ++ renderDefaultsValue v

def renderRunas (st : Settings) : Option RunasSpec → String
  | none | some ⟨none, none⟩ => s!"({st.runasDefault})"
  | some ⟨some us, none⟩ => s!"({renderMembers renderUserAtom us})"
  | some ⟨some us, some gs⟩ =>
    s!"({renderMembers renderUserAtom us} : {renderMembers renderUserAtom gs})"
  | some ⟨none, some gs⟩ => s!"(: {renderMembers renderUserAtom gs})"

/-- Options and tags of `cs`, printed when set and changed w.r.t. the previous spec. -/
def renderOptsTags (prev : Option CmndSpec) (cs : CmndSpec) : String :=
  let changed {β : Type} [BEq β] (get : CmndSpec → Option β) : Option β :=
    match get cs with
    | some v => if prev.map get == some (some v) then none else some v
    | none => none
  let cwd := match changed (·.options.cwd) with
    | some (some p) => s!"CWD={p} "
    | some none => "CWD=* "
    | none => ""
  let pw := match changed (·.tags.passwd) with
    | some true => "PASSWD: "
    | some false => "NOPASSWD: "
    | none => ""
  let se := match changed (·.tags.setenv) with
    | some true => "SETENV: "
    | some false => "NOSETENV: "
    | none => ""
  cwd ++ pw ++ se

/-- Lines (without the leading indentation's newline) for one `Host_List = Cmnd_Spec_List`. -/
def renderCmndSpecs (st : Settings) (cmnds : List CmndSpec) : List String :=
  go none "" cmnds
where
  go : Option CmndSpec → String → List CmndSpec → List String
    | none, _, [] => []
    | some _, cur, [] => [cur]
    | prev, cur, cs :: rest =>
      let body := renderOptsTags prev cs ++ renderMember renderCmndAtom cs.cmnd
      match prev with
      | some p =>
        if p.runas == cs.runas then go (some cs) (cur ++ ", " ++ body) rest
        else cur :: go (some cs) ("    " ++ renderRunas st cs.runas ++ " " ++ body) rest
      | none => go (some cs) ("    " ++ renderRunas st cs.runas ++ " " ++ body) rest

/-- The message for a user without any privileges on `host`. -/
def notAllowedMessage (user host : String) : String :=
  s!"User {user} is not allowed to run sudo on {host}."

/-- `sudo -l` output (see the module doc). -/
def listPrivileges (s : Sudoers) (st : Settings) (user : Principal) (host : String)
    (canon : String → String := id) : String :=
  let _ := canon -- command matching is not needed for listing
  let al := aliasesOf s
  let f := al.fuel
  let ds := defaultsOf s
  let matching := ds.flatMap fun
    | (.global, ss) => ss
    | (.host hs, ss) => if hostListOk al f host hs then ss else []
    | (.user us, ss) => if userListOk al f user us then ss else []
    | _ => []
  let bound :=
    (ds.filterMap fun
      | (.runas rs, ss) => some s!"    Defaults>{renderMembers renderUserAtom rs} {", ".intercalate (ss.map renderSetting)}"
      | _ => none) ++
    (ds.filterMap fun
      | (.cmnd cs, ss) => some s!"    Defaults!{renderMembers renderCmndAtom cs} {", ".intercalate (ss.map renderSetting)}"
      | _ => none)
  let privs := (specsOf s).flatMap fun us =>
    if userListOk al f user us.users then
      us.entries.flatMap fun hc =>
        if hostListOk al f host hc.hosts then renderCmndSpecs st hc.cmnds else []
    else []
  if privs.isEmpty then notAllowedMessage user.name host ++ "\n"
  else
    let defsSec :=
      if matching.isEmpty then ""
      else s!"Matching Defaults entries for {user.name} on {host}:\n    " ++
        ", ".intercalate (matching.map renderSetting) ++ "\n\n"
    let boundSec :=
      if bound.isEmpty then ""
      else s!"Runas and Command-specific defaults for {user.name}:\n" ++
        String.join (bound.map (· ++ "\n")) ++ "\n"
    defsSec ++ boundSec ++ s!"User {user.name} may run the following commands on {host}:\n" ++
      String.join (privs.map (· ++ "\n"))

end LeanSudo.Policy
