/-!
# POSIX `fnmatch(3)`

A total, structurally recursive implementation of the subset of `fnmatch(3)` that
sudo relies on:

* `*` matches any sequence of characters, `?` any single character;
* bracket expressions `[abc]`, ranges `[a-z]`, negation `[!x]` / `[^x]`, character
  classes `[[:alpha:]]`; a `]` right after the opening `[` (or `[!`) is literal;
  an unterminated `[` is a literal `[`;
* backslash escapes the next character (also inside brackets); a trailing
  backslash is literal;
* with `pathname` (`FNM_PATHNAME`), `*`, `?` and bracket expressions never match `/`;
* `caseInsensitive` (`FNM_CASEFOLD`) compares ASCII letters case-insensitively.

`FNM_PERIOD` is not implemented (sudo never passes it).

The pattern is first tokenised (`tokenize`), then matched (`matchToks`) by
structural recursion on the token list; `*` tries every suffix of the subject
(`anySuffix`).
-/

namespace LeanSudo.Glob

/-- One element of a bracket expression. -/
inductive BItem where
  | single (c : Char)
  | range (lo hi : Char)
  /-- `[:name:]` -/
  | cls (name : List Char)
  deriving Repr, BEq, Inhabited

inductive Tok where
  | lit (c : Char)
  /-- `?` -/
  | any
  /-- `*` -/
  | star
  | bracket (negated : Bool) (items : List BItem)
  deriving Repr, BEq, Inhabited

/-- Characters that make a pattern a glob (`*`, `?`, `[`) or that are interpreted
specially by `fnmatch` (`\`). -/
def isMeta (c : Char) : Bool := c == '*' || c == '?' || c == '[' || c == '\\'

/-- Does the pattern contain any character `fnmatch` treats specially? -/
def hasMeta (p : String) : Bool := p.toList.any isMeta

/-- Does the string contain a glob wildcard (`*`, `?` or `[`)? This is sudo's test for
"is this a pattern or a literal" in hosts, commands and arguments. -/
def hasGlob (p : String) : Bool := p.toList.any fun c => c == '*' || c == '?' || c == '['

/-- `name:]rest` ↦ `(name, rest)`. -/
def splitClass : List Char → Option (List Char × List Char)
  | [] => none
  | ':' :: ']' :: r => some ([], r)
  | c :: r => (splitClass r).map fun (n, r') => (c :: n, r')

/-- Read one possibly backslash-escaped character. -/
def readChar : List Char → Option (Char × List Char)
  | [] => none
  | ['\\'] => none
  | '\\' :: c :: r => some (c, r)
  | c :: r => some (c, r)

/-- Parse a bracket body (after `[` and the optional `!`/`^`). `first` is true at the
first position, where `]` is an ordinary member. Returns the items and the input after
the closing `]`, or `none` if the bracket is unterminated. -/
def parseBody : Nat → Bool → List Char → List BItem → Option (List BItem × List Char)
  | 0, _, _, _ => none
  | _ + 1, _, [], _ => none
  | _ + 1, false, ']' :: rest, acc => some (acc.reverse, rest)
  | n + 1, _, '[' :: ':' :: rest, acc =>
    match splitClass rest with
    | some (nm, r) => parseBody n false r (.cls nm :: acc)
    | none => parseBody n false (':' :: rest) (.single '[' :: acc)
  | n + 1, _, cs, acc =>
    match readChar cs with
    | none => none
    | some (c, r) =>
      match r with
      | '-' :: ']' :: _ => parseBody n false r (.single c :: acc)
      | '-' :: r2 =>
        match readChar r2 with
        | some (d, r3) => parseBody n false r3 (.range c d :: acc)
        | none => none
      | _ => parseBody n false r (.single c :: acc)

/-- Tokenise with fuel (`tokenize` passes the input length, which suffices since every
step consumes at least one character). -/
def tokF : Nat → List Char → List Tok
  | 0, _ => []
  | _ + 1, [] => []
  | _ + 1, ['\\'] => [.lit '\\']
  | n + 1, '\\' :: c :: r => .lit c :: tokF n r
  | n + 1, '*' :: r => .star :: tokF n r
  | n + 1, '?' :: r => .any :: tokF n r
  | n + 1, '[' :: r =>
    let (neg, body) : Bool × List Char :=
      match r with
      | '!' :: b => (true, b)
      | '^' :: b => (true, b)
      | b => (false, b)
    match parseBody body.length true body [] with
    | some (items, rest) => .bracket neg items :: tokF n rest
    | none => .lit '[' :: tokF n r
  | n + 1, c :: r => .lit c :: tokF n r

def tokenize (p : List Char) : List Tok := tokF p.length p

def lowerC (c : Char) : Char := c.toLower

def charEq (ci : Bool) (a b : Char) : Bool :=
  if ci then lowerC a == lowerC b else a == b

def classMatch (name : List Char) (c : Char) : Bool :=
  match String.ofList name with
  | "alpha" => c.isAlpha
  | "digit" => c.isDigit
  | "alnum" => c.isAlphanum
  | "upper" => c.isUpper
  | "lower" => c.isLower
  | "space" => c == ' ' || c == '\t' || c == '\n' || c == '\r' || c.toNat == 11 || c.toNat == 12
  | "blank" => c == ' ' || c == '\t'
  | "punct" => 33 ≤ c.toNat && c.toNat ≤ 126 && !c.isAlphanum
  | "print" => 32 ≤ c.toNat && c.toNat ≤ 126
  | "graph" => 33 ≤ c.toNat && c.toNat ≤ 126
  | "cntrl" => c.toNat < 32 || c.toNat == 127
  | "xdigit" => c.isDigit || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F')
  | _ => false

def inRange (lo hi c : Char) : Bool := lo ≤ c && c ≤ hi

def itemMatch (ci : Bool) (c : Char) : BItem → Bool
  | .single x => charEq ci x c
  | .range lo hi => inRange lo hi c || (ci && (inRange lo hi c.toLower || inRange lo hi c.toUpper))
  | .cls nm => classMatch nm c || (ci && (classMatch nm c.toLower || classMatch nm c.toUpper))

/-- `f` holds for some suffix of the subject reachable without skipping a `/` when
`pathname` is set. -/
def anySuffix (pathname : Bool) (f : List Char → Bool) : List Char → Bool
  | [] => f []
  | c :: cs => f (c :: cs) || (!(pathname && c == '/') && anySuffix pathname f cs)

def matchToks (pathname ci : Bool) : List Tok → List Char → Bool
  | [], s => s.isEmpty
  | .star :: ps, s => anySuffix pathname (matchToks pathname ci ps) s
  | _ :: _, [] => false
  | .lit c :: ps, d :: s => charEq ci c d && matchToks pathname ci ps s
  | .any :: ps, d :: s => !(pathname && d == '/') && matchToks pathname ci ps s
  | .bracket neg items :: ps, d :: s =>
    !(pathname && d == '/') && (items.any (itemMatch ci d) != neg) && matchToks pathname ci ps s

/-- POSIX `fnmatch(pattern, s, (pathname ? FNM_PATHNAME : 0) | (caseInsensitive ? FNM_CASEFOLD : 0)) == 0`. -/
def fnmatch (pattern s : String) (pathname : Bool) (caseInsensitive : Bool := false) : Bool :=
  matchToks pathname caseInsensitive (tokenize pattern.toList) s.toList

/-! ## Theorems -/

theorem tokF_nil (n : Nat) : tokF n [] = [] := by
  cases n <;> rfl

/-- A metacharacter-free prefix tokenises to literals. -/
theorem tokF_noMeta_append (cs rest : List Char) (h : cs.all (fun c => !isMeta c) = true) :
    ∀ n, tokF (n + cs.length) (cs ++ rest) = cs.map Tok.lit ++ tokF n rest := by
  induction cs with
  | nil => intro n; simp
  | cons c cs ih =>
    intro n
    simp only [List.all_cons, Bool.and_eq_true] at h
    obtain ⟨hc, hcs⟩ := h
    have e : n + (c :: cs).length = (n + cs.length) + 1 := by simp; omega
    rw [e]
    simp only [isMeta, Bool.not_or, Bool.and_eq_true, ne_eq, Bool.not_eq_true',
      beq_eq_false_iff_ne] at hc
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hc
    have step : tokF (n + cs.length + 1) (c :: (cs ++ rest)) = .lit c :: tokF (n + cs.length) (cs ++ rest) := by
      rw [tokF.eq_def]
      split <;> simp_all
    simp only [List.cons_append, List.map_cons, step, ih hcs n]

theorem tokenize_noMeta (cs : List Char) (h : cs.all (fun c => !isMeta c) = true) :
    tokenize cs = cs.map Tok.lit := by
  have := tokF_noMeta_append cs [] h 0
  simp only [List.append_nil, Nat.zero_add, tokF_nil] at this
  simpa [tokenize] using this

theorem matchToks_lits_append (pn : Bool) (cs : List Char) (ts : List Tok) :
    ∀ t, matchToks pn false (cs.map Tok.lit ++ ts) t = true ↔
      ∃ u, t = cs ++ u ∧ matchToks pn false ts u = true := by
  induction cs with
  | nil => intro t; simp
  | cons c cs ih =>
    intro t
    cases t with
    | nil => simp [matchToks]
    | cons d t =>
      simp only [List.map_cons, List.cons_append, matchToks, charEq, Bool.false_eq_true,
        ↓reduceIte, Bool.and_eq_true, beq_iff_eq, ih, List.cons.injEq]
      grind

theorem matchToks_lits (pn : Bool) (cs t : List Char) :
    matchToks pn false (cs.map Tok.lit) t = (cs == t) := by
  have := matchToks_lits_append pn cs [] t
  simp only [List.append_nil, matchToks, List.isEmpty_iff] at this
  cases h : (cs == t)
  · simp only [beq_eq_false_iff_ne] at h
    cases h' : matchToks pn false (cs.map Tok.lit) t
    · rfl
    · obtain ⟨u, rfl, rfl⟩ := this.mp h'; simp at h
  · simp only [beq_iff_eq] at h
    exact this.mpr ⟨[], by simp [h], rfl⟩

/-- **Literal patterns**: a pattern without metacharacters matches exactly itself. -/
theorem fnmatch_literal (p s : String) (pn : Bool) (h : hasMeta p = false) :
    fnmatch p s pn = (p == s) := by
  have h' : p.toList.all (fun c => !isMeta c) = true := by
    simpa [hasMeta, List.any_eq_false, List.all_eq_true] using h
  unfold fnmatch
  rw [tokenize_noMeta _ h', matchToks_lits]
  cases hps : (p == s)
  · simp only [beq_eq_false_iff_ne, ne_eq] at hps ⊢
    intro hl; exact hps (String.ext hl)
  · simp only [beq_iff_eq] at hps ⊢; rw [hps]

theorem anySuffix_nil_true (f : List Char → Bool) (hf : f [] = true) :
    ∀ s, anySuffix false f s = true := by
  intro s
  induction s with
  | nil => simpa [anySuffix] using hf
  | cons c cs ih => simp [anySuffix, ih]

/-- `*` without `pathname` matches everything. -/
theorem fnmatch_star (s : String) : fnmatch "*" s false = true := by
  have hs : "*".toList = ['*'] := by decide
  have ht : tokenize "*".toList = [Tok.star] := by rw [hs]; rfl
  simp only [fnmatch, ht, matchToks]
  exact anySuffix_nil_true _ (by simp) _

theorem anySuffix_pathname_empty (u : List Char) :
    anySuffix true (fun x : List Char => x.isEmpty) u = true ↔ '/' ∉ u := by
  induction u with
  | nil => simp [anySuffix]
  | cons c cs ih =>
    simp only [anySuffix, List.isEmpty_cons, Bool.true_and, Bool.false_or,
      Bool.and_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne, ih, List.mem_cons, not_or]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨fun h => h1 h.symm, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨fun h => h1 h.symm, h2⟩

/-- **`*` does not cross `/` with `pathname`**: a literal prefix followed by `*`
matches exactly the strings that extend the prefix by a `/`-free suffix. -/
theorem fnmatch_prefix_star_pathname (pre s : String) (h : hasMeta pre = false) :
    fnmatch (pre ++ "*") s true = true ↔ ∃ t : String, s = pre ++ t ∧ '/' ∉ t.toList := by
  have h' : pre.toList.all (fun c => !isMeta c) = true := by
    simpa [hasMeta, List.any_eq_false, List.all_eq_true] using h
  have htok : tokenize (pre ++ "*").toList = pre.toList.map Tok.lit ++ [Tok.star] := by
    have := tokF_noMeta_append pre.toList ['*'] h' 1
    simp only [tokenize, String.toList_append]
    have hl : (pre.toList ++ "*".toList).length = 1 + pre.toList.length := by
      simp; omega
    rw [hl]
    have hs : "*".toList = ['*'] := by decide
    rw [hs, this]
    rfl
  simp only [fnmatch, htok, matchToks_lits_append]
  simp only [matchToks]
  simp only [anySuffix_pathname_empty]
  constructor
  · rintro ⟨u, hu, hslash⟩
    refine ⟨String.ofList u, ?_, by simpa using hslash⟩
    apply String.ext; simp [hu]
  · rintro ⟨t, rfl, ht⟩
    exact ⟨t.toList, by simp, ht⟩

/-- Special case: with `pathname`, `*` matches exactly the `/`-free strings. -/
theorem fnmatch_star_pathname (s : String) : fnmatch "*" s true = true ↔ '/' ∉ s.toList := by
  simpa using fnmatch_prefix_star_pathname "" s (by decide)

end LeanSudo.Glob
