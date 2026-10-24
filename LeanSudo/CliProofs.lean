import LeanSudo.Cli

/-!
# Command-line theorems (DESIGN.md, verified property 7)

* `parseArgs_command`: the command vector is exactly the operand list the scanner
  stopped at, and `scan_suffix`: that list is a suffix of `argv[1..]` (sudo never
  rewrites, reorders or drops command words).
* `parseArgs_dashdash`: `--` ends option processing; everything after it is the command.
* `parseArgs_operand`: a first word that is not an option and not `VAR=value` starts the
  command; nothing after it is parsed as an option.
* Mutually exclusive options are rejected: `-i`/`-s`, `-i`/`-E`, `-i`/`-s` only with a
  command run, `-U` only with `-l`, `-A`/`-S`, edit mode needs files and takes no
  environment, run mode needs a command or a shell.
* `escapeJoin_wellEscaped` / `lex_escapeJoin`: the `-c` string for `-s`/`-i` contains no
  unescaped shell metacharacter, and splitting it the way the shell does gives back
  exactly the original words.
-/

namespace LeanSudo.Cli

/-! ## Operands -/

theorem scan_dashdash (rest : List String) (r : Raw) : scan ("--" :: rest) r = .ok (r, rest) := by
  have h : "--".toList = ['-', '-'] := by decide
  unfold scan
  rw [h]
  rfl

theorem scan_operand {a : String} {rest : List String} {r : Raw}
    (h1 : a.toList.head? ≠ some '-') (h2 : isEnvar a = false) :
    scan (a :: rest) r = .ok (r, a :: rest) := by
  unfold isEnvar at h2
  unfold scan
  split
  · rename_i heq; rw [heq] at h1; simp at h1
  · rename_i heq; rw [heq] at h1; simp at h1
  · rename_i heq; rw [heq] at h1; simp at h1
  · simp [h2]

theorem scan_suffix : ∀ (n : Nat) (args : List String) (r r' : Raw) (ops : List String),
    args.length ≤ n → scan args r = .ok (r', ops) → ops <:+ args := by
  intro n
  induction n with
  | zero =>
    intro args r r' ops hl h
    match args, hl with
    | [], _ =>
      unfold scan at h
      cases h
      exact List.nil_suffix
  | succ n ih =>
    intro args r r' ops hl h
    match args, hl with
    | [], _ =>
      unfold scan at h
      cases h
      exact List.nil_suffix
    | a :: rest, hl =>
      have hl' : rest.length ≤ n := by simp at hl; omega
      have hlt : rest.tail.length ≤ n := by simp; omega
      have sfx : rest <:+ a :: rest := List.suffix_cons a rest
      unfold scan at h
      split at h
      · cases h; exact sfx
      · split at h
        · cases h
        · exact (ih _ _ _ _ hlt h).trans ((List.tail_suffix rest).trans sfx)
        · exact (ih _ _ _ _ hl' h).trans sfx
      · split at h
        · cases h
        · exact (ih _ _ _ _ hlt h).trans ((List.tail_suffix rest).trans sfx)
        · exact (ih _ _ _ _ hl' h).trans sfx
      · split at h
        · exact (ih _ _ _ _ hl' h).trans sfx
        · cases h; exact List.suffix_refl _

theorem finish_eq {r : Raw} {ops : List String} {o : Options} (h : finish r ops = .ok o) :
    r.check ops = none ∧ o = r.build ops := by
  unfold finish at h
  split at h
  · cases h
  · rename_i hc; cases h; exact ⟨hc, rfl⟩

theorem parseArgs_eq {p : String} {args : List String} {o : Options} (h : parseArgs p args = .ok o) :
    ∃ r ops, scan args (Raw.init p) = .ok (r, ops) ∧ r.check ops = none ∧ o = r.build ops := by
  unfold parseArgs at h
  split at h
  · cases h
  · rename_i r ops hs
    obtain ⟨hc, rfl⟩ := finish_eq h
    exact ⟨r, ops, hs, hc, rfl⟩

/-- The command vector is exactly the operand list where option scanning stopped. -/
theorem parseArgs_command {p : String} {args : List String} {o : Options}
    (h : parseArgs p args = .ok o) : ∃ r, scan args (Raw.init p) = .ok (r, o.command) := by
  obtain ⟨r, ops, hs, -, rfl⟩ := parseArgs_eq h
  exact ⟨r, hs⟩

/-- The command is a suffix of the arguments: never rewritten, reordered or dropped. -/
theorem parseArgs_command_suffix {p : String} {args : List String} {o : Options}
    (h : parseArgs p args = .ok o) : o.command <:+ args := by
  obtain ⟨r, hs⟩ := parseArgs_command h
  exact scan_suffix _ _ _ _ _ (Nat.le_refl _) hs

/-- `--` stops option processing: everything after it is the command (even words that
look like options or `VAR=value`). -/
theorem parseArgs_dashdash {p : String} {rest : List String} {o : Options}
    (h : parseArgs p ("--" :: rest) = .ok o) : o.command = rest := by
  obtain ⟨r, hs⟩ := parseArgs_command h
  rw [scan_dashdash] at hs
  simp only [Except.ok.injEq, Prod.mk.injEq] at hs
  exact hs.2.symm

/-- A first word that does not start with `-` and is not `VAR=value` is the start of the
command; no option parsing happens after it. -/
theorem parseArgs_operand {p cmd : String} {rest : List String} {o : Options}
    (h1 : cmd.toList.head? ≠ some '-') (h2 : isEnvar cmd = false)
    (h : parseArgs p (cmd :: rest) = .ok o) : o.command = cmd :: rest := by
  obtain ⟨r, hs⟩ := parseArgs_command h
  rw [scan_operand h1 h2] at hs
  simp only [Except.ok.injEq, Prod.mk.injEq] at hs
  exact hs.2.symm

/-- The common special case: no leading `-` and no `=`. -/
theorem parseArgs_plain_command {p cmd : String} {rest : List String} {o : Options}
    (h1 : cmd.toList.head? ≠ some '-') (h2 : '=' ∉ cmd.toList)
    (h : parseArgs p (cmd :: rest) = .ok o) : o.command = cmd :: rest := by
  refine parseArgs_operand h1 ?_ h
  unfold isEnvar
  match hc : cmd.toList with
  | [] => rfl
  | c :: cs =>
    rw [hc] at h2
    unfold isEnvarL
    split <;> simp_all

/-! ## Validation -/

theorem check_none_rules {r : Raw} {ops : List String} (h : r.check ops = none) :
    ∀ c ∈ r.rules ops, c.1 = false := by
  unfold Raw.check at h
  cases hf : (r.rules ops).find? (·.1) with
  | some c => simp [hf] at h
  | none =>
    intro c hc
    have := List.find?_eq_none.1 hf c hc
    simpa using this

/-- What a successful validation guarantees about the parser state. -/
theorem check_none {r : Raw} {ops : List String} (h : r.check ops = none) :
    (r.login && r.shell) = false ∧
    (r.login && r.preserveAll) = false ∧
    (r.effMode ops == .edit && r.preserveAll) = false ∧
    (r.effMode ops == .edit && !(r.envVars.isEmpty && r.preserveVars.isEmpty)) = false ∧
    (!r.flagsValid (r.effMode ops)) = false ∧
    (r.otherUser.isSome && r.effMode ops != .list) = false ∧
    (r.stdin && r.askpass) = false ∧
    ((ops.isEmpty && r.effMode ops == .edit) ||
      (!ops.isEmpty && !(r.effMode ops == .run || r.effMode ops == .edit ||
        r.effMode ops == .list))) = false ∧
    (ops.isEmpty && r.effMode ops == .run && !(r.shell || r.login)) =
      (r.build ops).impliedShell := by
  have hall := check_none_rules h
  simp only [Raw.rules, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq] at hall
  obtain ⟨h1, h2, hf, h4, _, h6, h7, h8⟩ := hall
  refine ⟨h1, h2, ?_, h4, hf, h6, h7, h8, ?_⟩
  · cases hm : r.effMode ops <;> simp_all [Raw.flagsValid]
  · simp [Raw.build, Bool.and_comm]

theorem build_preserveEnv_all (r : Raw) (ops : List String) :
    (r.build ops).preserveEnv = .all ↔ r.preserveAll = true := by
  simp only [Raw.build]
  cases hpa : r.preserveAll <;> cases hpv : r.preserveVars.isEmpty <;> simp

/-- `-i` and `-s` are mutually exclusive. -/
theorem parseArgs_login_shell {p : String} {args : List String} {o : Options}
    (h : parseArgs p args = .ok o) : ¬(o.login = true ∧ o.shell = true) := by
  obtain ⟨r, ops, -, hc, rfl⟩ := parseArgs_eq h
  have c := (check_none hc).1
  rintro ⟨hl, hs⟩
  simp only [Raw.build] at hl hs
  simp [hl] at c hs
  simp [c] at hs

/-- `-i` and `-E` are mutually exclusive. -/
theorem parseArgs_login_preserve {p : String} {args : List String} {o : Options}
    (h : parseArgs p args = .ok o) : o.login = true → o.preserveEnv ≠ .all := by
  obtain ⟨r, ops, -, hc, rfl⟩ := parseArgs_eq h
  have c := (check_none hc).2.1
  intro hl hp
  rw [build_preserveEnv_all] at hp
  simp only [Raw.build] at hl
  simp [hl, hp] at c

/-- `-i`, `-s`, `-E`, `-H`, `-b`, `-P` are only accepted when running a command. -/
theorem parseArgs_run_flags {p : String} {args : List String} {o : Options}
    (h : parseArgs p args = .ok o)
    (hf : o.login = true ∨ o.shell = true ∨ o.preserveEnv = .all ∨ o.setHome = true ∨
      o.background = true ∨ o.preserveGroups = true) : o.mode = .run := by
  obtain ⟨r, ops, -, hc, rfl⟩ := parseArgs_eq h
  have c := (check_none hc).2.2.2.2.1
  rw [build_preserveEnv_all] at hf
  simp only [Raw.build] at hf ⊢
  clear h hc
  cases hm : r.effMode ops with
  | run => rfl
  | _ =>
    rw [hm] at c
    simp only [Raw.flagsValid, Bool.not_not] at c
    simp [hm] at hf
    rcases hf with hf | hf | hf | hf | hf | hf <;> simp [hf] at c

/-- `-U` requires `-l`. -/
theorem parseArgs_otherUser {p : String} {args : List String} {o : Options}
    (h : parseArgs p args = .ok o) (hu : o.otherUser.isSome = true) : o.mode = .list := by
  obtain ⟨r, ops, -, hc, rfl⟩ := parseArgs_eq h
  have c := (check_none hc).2.2.2.2.2.1
  simp only [Raw.build] at hu ⊢
  simpa [hu] using c

/-- `-A` and `-S` are mutually exclusive. -/
theorem parseArgs_askpass_stdin {p : String} {args : List String} {o : Options}
    (h : parseArgs p args = .ok o) : ¬(o.stdin = true ∧ o.askpass = true) := by
  obtain ⟨r, ops, -, hc, rfl⟩ := parseArgs_eq h
  have c := (check_none hc).2.2.2.2.2.2.1
  rintro ⟨h1, h2⟩
  simp only [Raw.build] at h1 h2
  simp [h1, h2] at c

/-- Edit mode needs at least one file and accepts no environment. -/
theorem parseArgs_edit {p : String} {args : List String} {o : Options}
    (h : parseArgs p args = .ok o) (he : o.mode = .edit) :
    o.command ≠ [] ∧ o.preserveEnv = .none ∧ o.envVars = [] := by
  obtain ⟨r, ops, -, hc, rfl⟩ := parseArgs_eq h
  obtain ⟨-, -, c3, c4, -, -, -, c8, -⟩ := check_none hc
  simp only [Raw.build] at he ⊢
  clear h hc
  rw [he] at c3 c4 c8
  simp at c3 c4 c8
  refine ⟨?_, ?_, ?_⟩
  · intro hn; simp [hn] at c8
  · cases hv : r.preserveVars.isEmpty <;> cases hn : r.envVars.isEmpty <;> simp_all
  · cases hv : r.preserveVars.isEmpty <;> cases hn : r.envVars.isEmpty <;> simp_all

/-- Run mode always has a command or an explicit/implied shell. -/
theorem parseArgs_run {p : String} {args : List String} {o : Options}
    (h : parseArgs p args = .ok o) (hr : o.mode = .run) :
    o.command ≠ [] ∨ o.shell = true ∨ o.login = true := by
  obtain ⟨r, ops, -, hc, rfl⟩ := parseArgs_eq h
  simp only [Raw.build] at hr ⊢
  cases hs : r.shell <;> cases hl : r.login <;> cases ho : ops <;> simp_all

/-- Only run, edit and list (check) modes take operands. -/
theorem parseArgs_operands_mode {p : String} {args : List String} {o : Options}
    (h : parseArgs p args = .ok o) (hne : o.command ≠ []) :
    o.mode = .run ∨ o.mode = .edit ∨ o.mode = .list := by
  obtain ⟨r, ops, -, hc, rfl⟩ := parseArgs_eq h
  have c := (check_none hc).2.2.2.2.2.2.2.1
  simp only [Raw.build] at hne ⊢
  clear h hc
  cases ho : ops with
  | nil => exact absurd ho hne
  | cons x xs =>
    rw [ho] at c
    cases hm : r.effMode (x :: xs) <;> simp_all

/-! ## Shell escaping -/

/-- Scanning left to right, every character is a `shellSafe` character, a separating
space, or the second half of a backslash escape. In particular no shell metacharacter
(`;`, `|`, `&`, `$(`, quotes, globs, redirections, newlines, ...) is unescaped. -/
inductive WellEscaped : List Char → Prop
  | nil : WellEscaped []
  | safe {c : Char} {r : List Char} : shellSafe c = true → WellEscaped r → WellEscaped (c :: r)
  | sep {r : List Char} : WellEscaped r → WellEscaped (' ' :: r)
  | esc {c : Char} {r : List Char} : WellEscaped r → WellEscaped ('\\' :: c :: r)

theorem wellEscaped_append {l r : List Char} (hl : WellEscaped l) (hr : WellEscaped r) :
    WellEscaped (l ++ r) := by
  induction hl with
  | nil => exact hr
  | safe hc _ ih => exact .safe hc ih
  | sep _ ih => exact .sep ih
  | esc _ ih => exact .esc ih

theorem escapeChars_wellEscaped (l : List Char) : WellEscaped (escapeChars l) := by
  induction l with
  | nil => exact .nil
  | cons c cs ih =>
    unfold escapeChars
    split
    · exact .safe (by assumption) ih
    · exact .esc ih

theorem escapeJoin_wellEscaped (ws : List String) : WellEscaped (escapeJoin ws) := by
  induction ws with
  | nil => exact .nil
  | cons w rest ih =>
    match rest, ih with
    | [], _ => exact escapeChars_wellEscaped _
    | w' :: rest', ih =>
      unfold escapeJoin
      exact wellEscaped_append (escapeChars_wellEscaped _) (.sep ih)

theorem shellEscape_wellEscaped (ws : List String) : WellEscaped (shellEscape ws).toList := by
  simp only [shellEscape, String.toList_ofList]
  exact escapeJoin_wellEscaped ws

/-- A minimal model of how a POSIX shell splits this restricted language into words:
backslash quotes the next character, an unquoted space separates words. -/
def lexAux : List Char → List Char → List (List Char)
  | [], cur => [cur]
  | '\\' :: c :: r, cur => lexAux r (cur ++ [c])
  | ' ' :: r, cur => cur :: lexAux r []
  | c :: r, cur => lexAux r (cur ++ [c])

theorem shellSafe_ne_space {c : Char} (h : shellSafe c = true) : c ≠ ' ' := by
  rintro rfl; simp [shellSafe] at h

theorem shellSafe_ne_backslash {c : Char} (h : shellSafe c = true) : c ≠ '\\' := by
  rintro rfl; simp [shellSafe] at h

theorem lexAux_safe {c : Char} (hc : shellSafe c = true) (r cur : List Char) :
    lexAux (c :: r) cur = lexAux r (cur ++ [c]) := by
  have h1 := shellSafe_ne_space hc
  have h2 := shellSafe_ne_backslash hc
  rw [lexAux.eq_def]
  split <;> simp_all

theorem lexAux_esc (c : Char) (r cur : List Char) :
    lexAux ('\\' :: c :: r) cur = lexAux r (cur ++ [c]) := by
  rw [lexAux.eq_def]
  rfl

theorem lexAux_space (r cur : List Char) : lexAux (' ' :: r) cur = cur :: lexAux r [] := by
  rw [lexAux.eq_def]
  rfl

theorem lexAux_escapeChars (w rest cur : List Char) :
    lexAux (escapeChars w ++ rest) cur = lexAux rest (cur ++ w) := by
  induction w generalizing cur with
  | nil => simp [escapeChars]
  | cons c cs ih =>
    unfold escapeChars
    split
    · rename_i hc
      rw [List.cons_append, lexAux_safe hc, ih]
      simp
    · rw [List.cons_append, List.cons_append, lexAux_esc, ih]
      simp

/-- Splitting the escaped string gives back exactly the original words (`ws ≠ []`). -/
theorem lex_escapeJoin (ws : List String) (h : ws ≠ []) :
    lexAux (escapeJoin ws) [] = ws.map String.toList := by
  induction ws with
  | nil => exact absurd rfl h
  | cons w rest ih =>
    match rest, ih with
    | [], _ =>
      have := lexAux_escapeChars w.toList [] []
      simp only [List.append_nil, List.nil_append] at this
      have e : escapeJoin [w] = escapeChars w.toList := rfl
      rw [e, this, lexAux.eq_def]
      simp
    | w' :: rest', ih =>
      have e : escapeJoin (w :: w' :: rest') =
          escapeChars w.toList ++ ' ' :: escapeJoin (w' :: rest') := rfl
      rw [e, lexAux_escapeChars, lexAux_space, ih (by simp)]
      simp

end LeanSudo.Cli
