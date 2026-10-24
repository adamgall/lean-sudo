namespace LeanSudo.Nsswitch

/-!
Ordered sudoers sources, matching sudo 1.9.17p2's sudo_nss.c. The first
case-insensitive sudoers line wins. Files and SSSD are supported; LDAP and
unknown sources remain explicit errors rather than falling back to local policy.
Return actions attach only to the immediately preceding newly added source.
The source selector retains global Defaults from every source, but never
consults authorization entries beyond a terminal action.
-/

private def blank (c : Char) : Bool := c == ' ' || c == '\t'

private def trimStart (s : String) : String :=
  String.ofList (s.toList.dropWhile blank)

private def trimEnd (s : String) : String :=
  String.ofList ((s.toList.reverse.dropWhile blank).reverse)

private def physicalLine (s : String) : String × Bool := Id.run do
  let s := String.ofList ((s.toList.reverse.dropWhile (· == '\r')).reverse)
  let pieces := s.splitOn "#"
  let body := pieces.headD ""
  let continued := pieces.length == 1 && body.endsWith "\\" && !body.endsWith "\\\\"
  let body := if continued then String.ofList (body.toList.dropLast) else trimEnd body
  return (trimStart body, continued)

private def joinLines : List String → String → List String
  | [], pending => if pending.isEmpty then [] else [pending]
  | line :: rest, pending =>
    let (body, continued) := physicalLine line
    if continued then joinLines rest (pending ++ body)
    else (pending ++ body) :: joinLines rest ""

/-- Normalized source tokens. Recognized actions are not sources. Unknown action
clauses are diagnosed separately; in particular they never swallow later sources. -/
private def sourceTokens : List String → Except String (List String)
  | [] => .ok []
  | token :: rest => do
    let token := token.toLower
    if token == "[success=return]" || token == "[notfound=return]" then
      sourceTokens rest
    else if token.startsWith "[" || token.endsWith "]" then
      throw ("/etc/nsswitch.conf: unsupported sudoers action: " ++ token)
    else
      return token :: (← sourceTokens rest)

private def firstEntry : List String → Except String (List String)
  | [] => .ok ["files"]
  | line :: rest =>
    if line.toLower.startsWith "sudoers:" then
      sourceTokens ((String.ofList (line.toList.drop 8)).splitOn " "
        |>.flatMap (·.splitOn "\t") |>.filter (!·.isEmpty))
    else firstEntry rest

/-- Parse the first sudoers entry, preserving every configured source. The
absence of an entry is distinct from an explicit entry with no sources. -/
def parse (text : String) : Except String (List String) :=
  if text.toList.contains '\x00' then
    .error "/etc/nsswitch.conf: invalid NUL in configuration"
  else firstEntry (joinLines (text.splitOn "\n") "")

private def checkSources : List String → Except String Unit
  | [] => .ok ()
  | source :: rest =>
    if source = "files" ∨ source = "sss" then checkSources rest
    else .error ("/etc/nsswitch.conf: unsupported sudoers source: " ++ source)

/-- Approval requires at least one supported backend and no unsupported source. -/
def approveSources : List String → Except String Unit
  | [] => .error "/etc/nsswitch.conf: sudoers entry has no files source"
  | source :: rest => checkSources (source :: rest)

/-- The shell must call this before Sudoers.load, and must not load policy after
an error. Only a missing nsswitch.conf may be supplied as empty text; other IO
errors must not silently select the files backend. -/
def approve (text : String) : Except String Unit := do
  approveSources (← parse text)

private theorem checkSources_supported_only (sources : List String)
    (h : checkSources sources = .ok ()) :
    ∀ source ∈ sources, source = "files" ∨ source = "sss" := by
  induction sources with
  | nil => simp
  | cons source rest ih =>
    by_cases hs : source = "files" ∨ source = "sss"
    · have hr : checkSources rest = .ok () := by
        simpa [checkSources, hs] using h
      intro candidate hc
      rcases List.mem_cons.mp hc with hc | hc
      · subst candidate; exact hs
      · exact ih hr candidate hc
    · simp [checkSources, hs] at h

/-- Approval cannot silently ignore a configured backend or approve an empty
source list. This is the condition needed before consulting local sudoers. -/
theorem approveSources_supported_only (sources : List String)
    (h : approveSources sources = .ok ()) :
    sources ≠ [] ∧ ∀ source ∈ sources, source = "files" ∨ source = "sss" := by
  cases sources with
  | nil => simp [approveSources] at h
  | cons source rest =>
    exact ⟨by simp, checkSources_supported_only _ h⟩

/-- Successful approval cannot silently ignore an unsupported source. -/
theorem approve_supported_only (text : String) (sources : List String)
    (parsed : parse text = .ok sources) (h : approve text = .ok ()) :
    sources ≠ [] ∧ ∀ source ∈ sources, source = "files" ∨ source = "sss" := by
  unfold approve at h
  rw [parsed] at h
  exact approveSources_supported_only sources h

structure Source where
  name : String
  returnIfFound : Bool := false
  returnIfNotFound : Bool := false
  deriving Repr, BEq, Inhabited

/-- Match denotes a specified allow or deny, not merely an allow. -/
def canContinue (source : Source) (found : Bool) : Bool :=
  !(source.returnIfNotFound && !found || source.returnIfFound && found)

private def rawEntry : List String → List String
  | [] => ["files"]
  | line :: rest =>
    if line.toLower.startsWith "sudoers:" then
      ((String.ofList (line.toList.drop 8)).splitOn " "
        |>.flatMap (·.splitOn "\t") |>.filter (!·.isEmpty)).map String.toLower
    else rawEntry rest

def configure (text : String) : Except String (List Source) := do
  approve text
  let mut sources : List Source := []
  let mut attached := false
  for token in rawEntry (joinLines (text.splitOn "\n") "") do
    if token == "files" || token == "sss" then
      if sources.any (·.name == token) then attached := false
      else
        sources := { name := token } :: sources
        attached := true
    else
      if attached then
        sources := sources.modifyHead fun s =>
          if token == "[success=return]" then { s with returnIfFound := true }
          else if token == "[notfound=return]" then { s with returnIfNotFound := true }
          else s
      attached := false
  return sources.reverse

/-- Retain the visited prefix. Pseudo-command lookup passes cumulative matches;
execution passes the current source's match, as lookup.c does. -/
def select {α : Type} (hasMatch : α → Bool) (pseudo : Bool) :
    List (Source × α) → Bool → List α
  | [], _ => []
  | (source, policy) :: rest, previous =>
    let found := hasMatch policy || (pseudo && previous)
    policy :: if canContinue source found then select hasMatch pseudo rest found else []

theorem select_terminal {α : Type} (hasMatch : α → Bool) (pseudo : Bool)
    (source : Source) (policy : α) (rest : List (Source × α)) (previous : Bool)
    (h : canContinue source (hasMatch policy || (pseudo && previous)) = false) :
    select hasMatch pseudo ((source, policy) :: rest) previous = [policy] := by
  simp [select, h]

theorem notfound_return_stops (name : String) :
    canContinue { name, returnIfNotFound := true } false = false := rfl

end LeanSudo.Nsswitch
