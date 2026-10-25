import LeanSudo.Sys.Exec

namespace LeanSudo.Sudoedit

def pathParts (path : String) : Option (List String × String) := do
  if !path.startsWith "/" || !Sys.Exec.cSafe path then none
  else
    match (path.splitOn "/").reverse with
    | [] => none
    | name :: dirs => some ((dirs.reverse).filter (· != ""), if name == "" then "." else name)

private def unescapeWord : List Char → List Char
  | '\\' :: c :: cs => c :: unescapeWord cs
  | c :: cs => c :: unescapeWord cs
  | [] => []

private def quotedWord (quote : Char) : List Char → Bool → List Char →
    Option (List Char × List Char)
  | [], _, _ => none
  | c :: cs, escaped, acc =>
    if c == quote && !escaped then some (acc.reverse, cs)
    else quotedWord quote cs (c == '\\') (c :: acc)

private def bareWord : List Char → List Char → List Char × List Char
  | [], acc => (acc.reverse, [])
  | '\\' :: c :: cs, acc => bareWord cs (c :: '\\' :: acc)
  | c :: cs, acc =>
    if c == ' ' || c == '\t' then (acc.reverse, cs)
    else bareWord cs (c :: acc)

private def splitEditor : Nat → List Char → List String
  | 0, _ => []
  | fuel + 1, chars =>
    match chars.dropWhile (fun c => c == ' ' || c == '\t') with
    | [] => []
    | c :: cs =>
      let (word, rest) := if c == '\'' || c == '"' then
        match quotedWord c cs false [] with
        | some result => result
        | none => bareWord (c :: cs) []
        else bareWord (c :: cs) []
      String.ofList (unescapeWord word) :: splitEditor fuel rest

def editorWords (source : String) : List String :=
  splitEditor (source.length + 1) source.toList

def tempName (name : String) : String :=
  match (name.splitOn ".").reverse with
  | suffix :: rest@(_ :: _) => String.intercalate "." rest.reverse ++ "XXXXXXXX." ++ suffix
  | _ => name ++ ".XXXXXXXX"

def fileChanged (before after : Array Nat) (elapsed : Bool) : Bool :=
  !elapsed || before[3]! != after[3]! || before[4]! != after[4]! || before[5]! != after[5]!
def editorArgsSafe (words : List String) : Bool :=
  !words.isEmpty && words.all Sys.Exec.cSafe && !(words.drop 1).contains "--"

theorem editorWords_no_file_separator (source : String)
    (h : editorArgsSafe (editorWords source) = true) :
    "--" ∉ (editorWords source).drop 1 := by
  simp [editorArgsSafe, Bool.and_eq_true] at h
  simpa using h.2
def selectEditor : List (List String × Option String) → Option (String × List String)
  | [] => none
  | (words, some path) :: _ => some (path, words)
  | (_, none) :: rest => selectEditor rest

theorem selectEditor_first (words : List String) (path : String) (rest) :
    selectEditor ((words, some path) :: rest) = some (path, words) := rfl

theorem selectEditor_skip (words : List String) (rest) :
    selectEditor ((words, none) :: rest) = selectEditor rest := rfl

theorem selectEditor_prefix (before : List (List String × Option String))
    (h : ∀ c ∈ before, c.2 = none) (words : List String) (path : String) (rest) :
    selectEditor (before ++ (words, some path) :: rest) = some (path, words) := by
  induction before with
  | nil => rfl
  | cons c cs ih =>
    have hc := h c (by simp)
    obtain ⟨w, p⟩ := c
    simp only at hc
    subst p
    simp only [List.cons_append, selectEditor]
    apply ih
    intro c hm
    exact h c (by simp [hm])

def tempSafe (regular owned singleLink : Bool) : Bool := regular && owned && singleLink

def writeBack (changed checked : Bool) : Bool := changed && checked

theorem writeBack_sound {changed checked : Bool} (h : writeBack changed checked = true) :
    changed = true ∧ checked = true := by
  simpa [writeBack] using h

theorem tempSafe_sound {regular owned singleLink : Bool}
    (h : tempSafe regular owned singleLink = true) :
    regular = true ∧ owned = true ∧ singleLink = true := by
  simpa [tempSafe, Bool.and_eq_true, and_assoc] using h

end LeanSudo.Sudoedit
