import LeanSudo.Sys.Exec

namespace LeanSudo.Sudoedit

/-- Reject traversal, NUL and empty final names before descriptor-relative opens.
Intermediate symbolic links are deliberately refused as well as final links. -/
def pathParts (path : String) : Option (List String × String) := do
  if !path.startsWith "/" || !Sys.Exec.cSafe path || path.endsWith "/" then none
  else
    let parts := (path.splitOn "/").filter (· != "")
    if parts.any (fun p => p == "." || p == "..") then none
    else match parts.reverse with
      | [] => none
      | name :: dirs => some (dirs.reverse, name)

/-- The editor cannot inject additional sudoedit file operands via `--`. -/
def editorArgsSafe (words : List String) : Bool :=
  !words.isEmpty && words.all Sys.Exec.cSafe && !words.contains "--"

/-- Ordered candidate selection from filesystem resolution results. -/
def selectEditor : List (List String × Option String) → Option (String × List String)
  | [] => none
  | (words, some path) :: _ => some (path, words)
  | (_, none) :: rest => selectEditor rest

theorem selectEditor_first (words : List String) (path : String) (rest) :
    selectEditor ((words, some path) :: rest) = some (path, words) := rfl

theorem selectEditor_skip (words : List String) (rest) :
    selectEditor ((words, none) :: rest) = selectEditor rest := rfl

/-- Every skipped candidate preceding the chosen candidate was unresolved. -/
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

/-- Copyback is authorized only for a changed, checked temporary file. -/
def writeBack (changed checked : Bool) : Bool := changed && checked

theorem writeBack_sound {changed checked : Bool} (h : writeBack changed checked = true) :
    changed = true ∧ checked = true := by
  simpa [writeBack] using h

theorem tempSafe_sound {regular owned singleLink : Bool}
    (h : tempSafe regular owned singleLink = true) :
    regular = true ∧ owned = true ∧ singleLink = true := by
  simpa [tempSafe, Bool.and_eq_true, and_assoc] using h

end LeanSudo.Sudoedit
