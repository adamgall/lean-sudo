import LeanSudo.SudoConf

namespace LeanSudo.Nsswitch

/-!
Ordered sudoers sources, matching sudo 1.9.17p2's sudo_nss.c. The first
case-insensitive sudoers line wins. Ubuntu supports files and SSSD, silently
ignores other tokens, and defaults to files when no supported source remains.
Return actions attach only to the immediately preceding newly added source.
The source selector retains global Defaults from every source, but never
consults authorization entries beyond a terminal action.
-/

structure Source where
  name : String
  returnIfFound : Bool := false
  returnIfNotFound : Bool := false
  deriving Repr, BEq, Inhabited

/-- Match denotes a specified allow or deny, not merely an allow. -/
def canContinue (source : Source) (found : Bool) : Bool :=
  !(source.returnIfNotFound && !found || source.returnIfFound && found)

private def rawEntry (text : String) : List String :=
  (SudoConf.foldLogicalLinesM (m := Id) true (fun (found : Option (List String)) _ line =>
    if found.isNone && line.toLower.startsWith "sudoers:" then
      some ((SudoConf.words (String.ofList (line.toList.drop 8))).map String.toLower)
    else found) none text).getD ["files"]

private def sourceStep (state : List Source × Bool) (token : String) : List Source × Bool :=
  let (sources, attached) := state
  if token == "files" || token == "sss" then
    if sources.any (·.name == token) then (sources, false)
    else ({ name := token } :: sources, true)
  else
    let sources := match sources with
      | [] => []
      | source :: rest =>
        { source with
          returnIfFound := source.returnIfFound || (attached && token == "[success=return]")
          returnIfNotFound := source.returnIfNotFound || (attached && token == "[notfound=return]") } :: rest
    (sources, false)

private theorem sourceStep_supported (state : List Source × Bool) (token : String)
    (h : ∀ source ∈ state.1, source.name = "files" ∨ source.name = "sss") :
    ∀ source ∈ (sourceStep state token).1, source.name = "files" ∨ source.name = "sss" := by
  rcases state with ⟨sources, attached⟩
  dsimp only [sourceStep]
  split
  · rename_i ht
    split
    · exact h
    · intro source hs
      rcases List.mem_cons.mp hs with hs | hs
      · subst source
        simpa only [Bool.or_eq_true, beq_iff_eq] using ht
      · exact h source hs
  · cases sources with
    | nil => simp
    | cons source rest =>
      intro candidate hc
      rcases List.mem_cons.mp hc with hc | hc
      · subst candidate
        exact h source (by simp)
      · exact h candidate (by simp [hc])

private theorem checkSources_supported_only (tokens : List String) (state : List Source × Bool)
    (h : ∀ source ∈ state.1, source.name = "files" ∨ source.name = "sss") :
    ∀ source ∈ (tokens.foldl sourceStep state).1,
      source.name = "files" ∨ source.name = "sss" := by
  induction tokens generalizing state with
  | nil => exact h
  | cons token rest ih => exact ih _ (sourceStep_supported state token h)

/-- Select compiled-in backends from normalized tokens, retaining order and
return actions. Unrecognized tokens break action attachment, but never warn.
An empty selection falls back to files, not an unavailable supported backend. -/
def approveSources (tokens : List String) : List Source :=
  let sources := (tokens.foldl sourceStep ([], false)).1
  if sources = [] then [{ name := "files" }] else sources.reverse

/-- Every backend the runtime can consult is supported, and selection is never
empty. This applies to the selected chain, not ignored configuration words. -/
theorem approveSources_supported_only (tokens : List String) :
    approveSources tokens ≠ [] ∧ ∀ source ∈ approveSources tokens,
      source.name = "files" ∨ source.name = "sss" := by
  have supported := checkSources_supported_only tokens ([], false) (by simp)
  dsimp only [approveSources]
  split
  · constructor
    · simp
    · intro source hs
      simp only [List.mem_singleton] at hs
      subst source
      simp
  · rename_i nonempty
    constructor
    · intro h
      apply nonempty
      simpa using congrArg List.reverse h
    · intro source hs
      exact supported source (by simpa using hs)

/-- Parse the first sudoers entry. Unsupported source/action words are ignored
as in sudo_nss.c; no recognized source means the ordinary files default. -/
def configure (text : String) : Except String (List Source) :=
  if text.toList.contains '\x00' then
    .error "/etc/nsswitch.conf: invalid NUL in configuration"
  else .ok (approveSources (rawEntry text))

/-- The configured runtime chain is nonempty and contains only files/SSSD.
In particular, an explicit supported SSSD source is not replaced by files. -/
theorem approve_supported_only (text : String) (sources : List Source)
    (configured : configure text = .ok sources) :
    sources ≠ [] ∧ ∀ source ∈ sources, source.name = "files" ∨ source.name = "sss" := by
  unfold configure at configured
  split at configured
  · contradiction
  · cases Except.ok.inj configured
    exact approveSources_supported_only _

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
