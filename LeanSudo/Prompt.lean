namespace LeanSudo

def expandPromptL (u U h p : List Char) : List Char → List Char
  | [] => []
  | '%' :: 'u' :: r => u ++ expandPromptL u U h p r
  | '%' :: 'U' :: r => U ++ expandPromptL u U h p r
  | '%' :: 'h' :: r => h.takeWhile (· != '.') ++ expandPromptL u U h p r
  | '%' :: 'H' :: r => h ++ expandPromptL u U h p r
  | '%' :: 'p' :: r => p ++ expandPromptL u U h p r
  | '%' :: '%' :: r => '%' :: expandPromptL u U h p r
  | c :: r => c :: expandPromptL u U h p r

def expandPrompt (fmt : String) (user target host authUser : String) : String :=
  String.ofList (expandPromptL user.toList target.toList host.toList authUser.toList fmt.toList)

theorem expandPromptL_no_percent (u U h p l : List Char) (hl : '%' ∉ l) :
    expandPromptL u U h p l = l := by
  induction l with
  | nil => rfl
  | cons c r ih =>
    have hc : c ≠ '%' := fun e => hl (e ▸ List.mem_cons_self)
    have hr : '%' ∉ r := fun m => hl (List.mem_cons_of_mem _ m)
    unfold expandPromptL
    split <;> simp_all

theorem expandPrompt_no_percent (fmt u U h p : String) (hl : '%' ∉ fmt.toList) :
    expandPrompt fmt u U h p = fmt := by
  simp [expandPrompt, expandPromptL_no_percent _ _ _ _ _ hl]

end LeanSudo
