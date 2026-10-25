import LeanSudo.Sudoers.Parser
import LeanSudo.Policy.Eval
import LeanSudo.SudoConf

/-! SSSD's wire result is already sorted by descending sudoOrder. Conversion
reverses that order, just like sssd.c, and partitions negative LDAP members to
last position (ldap_util.c). Values are data, never reparsed as sudoers lines. -/
namespace LeanSudo.Sss
open Sudoers
open SudoConf (blank trimStart trimEnd)

abbrev Rule := Array (String × Array String)

def values (r : Rule) (name : String) : List String :=
  let key := name.toLower
  ((r.find? fun a => a.1.toLower == key).map (·.2.toList)).getD []

/-- Toggle every leading !, ignoring intervening horizontal whitespace. -/
def negation (text : String) : Bool × String := Id.run do
  let mut chars := text.toList
  let mut neg := false
  for _ in text.toList do
    if chars.head? != some '!' then break
    neg := !neg
    chars := chars.drop 1 |>.dropWhile blank
  return (neg, String.ofList chars)

/-- Stable partition: an exclusion always follows all positive members. -/
def negativesLast {α : Type} (negative : α → Bool) (xs : List α) : List α :=
  xs.filter (fun x => !negative x) ++ xs.filter negative

theorem negativesLast_mem {α : Type} (negative : α → Bool) (xs : List α) (x : α) :
    x ∈ negativesLast negative xs ↔ x ∈ xs := by
  simp only [negativesLast, List.mem_append, List.mem_filter]
  cases negative x <;> simp

theorem negativesLast_exclusion_suffix {α : Type} (negative : α → Bool) (xs : List α) :
    negativesLast negative xs = xs.filter (fun x => !negative x) ++ xs.filter negative := rfl

/-- ldap_util.c sudo_ldap_parse_option; unlike sudoers, values are not tokenized. -/
def parseOption (text : String) : DefaultsSetting := Id.run do
  let parts := text.splitOn "="
  if parts.length > 1 && !(parts.headD "").isEmpty then
    let lhs := parts.headD ""
    let op := lhs.toList.getLast?
    let name := trimEnd (if op == some '+' || op == some '-' then (lhs.dropEnd 1).toString else lhs)
    let value := trimStart ("=".intercalate (parts.drop 1))
    let value := if value.startsWith "\"" && value.endsWith "\"" then
        (value.drop 1).toString.dropEnd 1 |>.toString else value
    return { name, op := if op == some '+' then .add value else if op == some '-' then .remove value else .assign value }
  let (neg, name) := negation text
  return { name, op := .flag (!neg) }

def userAtom (text : String) : UserAtom :=
  if text == "ALL" then .all
  else if text.isEmpty then .myself
  else if text.startsWith "+" then .netgroup (text.drop 1).toString
  else if text.startsWith "%:#" then
    ((text.drop 3).toString.toNat?.map UserAtom.nonunixGid).getD (.nonunixGroup (text.drop 2).toString)
  else if text.startsWith "%:" then .nonunixGroup (text.drop 2).toString
  else if text.startsWith "%#" then
    ((text.drop 2).toString.toNat?.map UserAtom.gid).getD (.group (text.drop 1).toString)
  else if text.startsWith "%" then .group (text.drop 1).toString
  else if text.startsWith "#" then
    ((text.drop 1).toString.toNat?.map UserAtom.id).getD (.name text)
  else .name text

def userMembers (xs : List String) : List (Member UserAtom) :=
  negativesLast (·.negated) (xs.map fun text =>
    let (neg, text) := negation text
    ⟨neg, userAtom text⟩)

/-- sssd.c rechecks sudoUser in wire order and stops on its first match.
Only one ! is stripped there (unlike LDAP run-as, host and command members). -/
def invokingMembers (xs : List String) : List (Member UserAtom) :=
  (xs.map fun text =>
    let neg := text.startsWith "!"
    { negated := neg, atom := userAtom (if neg then (text.drop 1).toString else text) }).reverse

def hostMembers (xs : List String) : List (Member HostAtom) :=
  negativesLast (·.negated) (xs.map fun text =>
    let (neg, text) := negation text
    let atom := if text == "ALL" then .all else if text.startsWith "+" then
      .netgroup (text.drop 1).toString else (Parser.network text).getD (.name text)
    ⟨neg, atom⟩)

/-- LDAP commands split at the first single blank; remaining argument bytes,
including additional blanks, quotes and sudoers punctuation, stay literal. -/
def command (text : String) : Except String (Member CmndAtom) := do
  let (neg, text) := negation text
  let (digests, rest) ← match (Parser.readDigests (Parser.context "SSSD" text)).run
      { input := Parser.annotate text.toList 1 1 [] } with
    | .ok result => pure result
    | .error e => throw e.toString
  let text := String.ofList (rest.input.map (·.c))
  let pathChars := text.toList.takeWhile (!blank ·)
  let path := String.ofList pathChars
  let argsText := String.ofList (text.toList.drop (pathChars.length + 1))
  let args := if pathChars.length == text.length then CmndArgs.any
    else if argsText == "\"\"" then .none
    else if argsText.startsWith "^" && argsText.endsWith "$" then .regex argsText
    else .pattern argsText
  let atom := if text == "ALL" then .all else if path == "sudoedit" then .sudoedit args
    else if path == "list" then .list
    else if path.startsWith "^" && path.endsWith "$" then .commandRegex path args
    else .command path args
  return ⟨neg, if digests.isEmpty then atom else .digest digests atom⟩

private def optionValue (d : DefaultsSetting) : Option String :=
  match d.op with | .assign v | .add v | .remove v => some v | _ => none

private def specialOptions : List String :=
  ["command_timeout", "runchroot", "runcwd", "role", "type", "apparmor_profile", "privs", "limitprivs"]

private def options (r : Rule) : CmndOptions := Id.run do
  let mut o : CmndOptions := {
    notBefore := (values r "sudoNotBefore").head?.bind Parser.parseGentime
    notAfter := (values r "sudoNotAfter").head?.bind Parser.parseGentime
    notBeforeLocal := (values r "sudoNotBefore").head?.any
      (fun s => !s.endsWith "Z" && !s.contains '+' && !s.contains '-')
    notAfterLocal := (values r "sudoNotAfter").head?.any
      (fun s => !s.endsWith "Z" && !s.contains '+' && !s.contains '-') }
  for raw in values r "sudoOption" do
    let d := parseOption raw
    if let some v := optionValue d then
      o := match d.name with
        | "command_timeout" => { o with timeout := Parser.parseTimeout v }
        | "runchroot" => { o with chroot := some v }
        | "runcwd" => { o with cwd := some (if v == "*" then none else some v) }
        | "role" => { o with role := some v }
        | "type" => { o with type := some v }
        | "apparmor_profile" => { o with apparmorProfile := some v }
        | "privs" => { o with privs := some v }
        | "limitprivs" => { o with limitprivs := some v }
        | _ => o
  return o

/-- Tags are a projection for the existing evaluator and short listing. Full
privilege Defaults are applied only to the winning privilege by the shell. -/
def optionTags (xs : List String) : Tags := xs.foldl (fun tags raw =>
  let d := parseOption raw
  match d.op with
  | .flag b => match d.name with
    | "authenticate" => { tags with passwd := some b }
    | "setenv" => { tags with setenv := some b }
    | "noexec" => { tags with noexec := some b }
    | "intercept" => { tags with intercept := some b }
    | "log_input" => { tags with logInput := some b }
    | "log_output" => { tags with logOutput := some b }
    | "sudoedit_follow" => { tags with follow := some b }
    | "mail_all_cmnds" => { tags with mail := some b }
    | _ => tags
  | _ => tags) {}

def role (r : Rule) : Except String (Option Located) := do
  let some name := (values r "cn").head? | return none
  let cmds := values r "sudoCommand"
  let hosts := values r "sudoHost"
  if cmds.isEmpty || hosts.isEmpty then return none
  let users := values r "sudoRunAsUser"
  let users := if users.isEmpty then values r "sudoRunAs" else users
  let groups := values r "sudoRunAsGroup"
  let runas := if users.isEmpty && groups.isEmpty then none else
    some { users := if users.isEmpty then none else some (userMembers users)
           groups := if groups.isEmpty then none else some (userMembers groups) }
  let opts := (values r "sudoOption").filter fun raw =>
    let d := parseOption raw
    !(specialOptions.contains d.name && (optionValue d).isSome)
  let tags := optionTags opts
  let cmndOptions := options r
  let commands ← cmds.mapM command
  let cmnds := (negativesLast (·.negated) commands).map fun cmnd =>
    { runas, options := cmndOptions,
      tags := if cmnd.atom == .all then { tags with setenv := none } else tags,
      cmnd, ldapRole := some name, ldapOptions := opts : CmndSpec }
  return some { file := "SSSD", line := 1, entry := .userSpec {
    users := invokingMembers (values r "sudoUser"), entries := [{ hosts := hostMembers hosts, cmnds }] } }

/-- Do not sort textually or round sudoOrder: SSSD has already performed its
numeric sort. Reverse its result exactly (including its equal-order tie order). -/
def convert (defaults rules : Array Rule) : Except String (List Located) := do
  let ds := defaults.toList.map fun r =>
    { file := "sudoRole " ++ ((values r "cn").headD "UNKNOWN"), line := 1,
      entry := .defaults .global ((values r "sudoOption").map parseOption) : Located }
  return ds ++ (← rules.toList.reverse.filterMapM role)
/-- sssd.c uses the first nonempty ipa_hostname assignment (independent of domain). -/
def ipaHostname (text : String) : Option String :=
  (text.splitOn "\n").findSome? fun line => do
    let line := line.trimAscii.toString
    if !line.startsWith "ipa_hostname" then none else do
      let rest := trimStart (line.drop 12).toString
      if !rest.startsWith "=" then none else do
        let value := trimStart (rest.drop 1).toString
        if value.isEmpty then none else some value

/-- SSSD's optional IPA hostname belongs to that backend alone. Resolve user
and host lists against that hostname, without changing the files backend. -/
def withIpaHost (entries : List Located) (st : Settings) (facts : Request)
    (subjects : List Principal) (hostname : String) : List Located :=
  let facts := { facts with host := (hostname.splitOn ".").headD hostname, lhost := hostname }
  let al : Policy.Aliases := {}
  entries.map fun located => match located.entry with
    | .userSpec us =>
      let users := subjects.filter fun p =>
        Policy.userListOk al al.fuel p us.users st (some { facts with user := p })
      let hosts := us.entries.filterMap fun hc =>
        if Policy.hostListOk al al.fuel facts.host hc.hosts st (some facts) then
          some { hc with hosts := [⟨false, .all⟩] }
        else none
      { located with entry := .userSpec { us with
          users := users.map (fun p => ⟨false, .name p.name⟩), entries := hosts } }
    | _ => located


theorem convert_empty : convert #[] #[] = .ok [] := rfl

end LeanSudo.Sss
