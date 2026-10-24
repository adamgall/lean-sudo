import LeanSudo.Policy.Types

/-!
# Timestamp records (pure)

Pure model of sudo's credential cache ("timestamp") file: record identity (scope),
validity, update / invalidation, and a versioned binary encoding with a proved
roundtrip. All IO lives in `LeanSudo.Sys.Timestamp`.

Times are `CLOCK_BOOTTIME` nanoseconds; timeouts are seconds (as in sudoers).
-/

namespace LeanSudo.Timestamp

/-- What a cached credential is bound to (sudo's `timestamp_type`). Start times
(clock ticks since boot, `/proc/<pid>/stat` field 22) guard against pid reuse. -/
inductive Scope where
  /-- terminal device number, session id, start time of the session leader -/
  | tty (dev : Nat) (sid : Nat) (sidStart : Nat)
  /-- parent process id and its start time -/
  | ppid (pid : Nat) (start : Nat)
  | global
  deriving DecidableEq, Repr, Inhabited

structure Record where
  scope : Scope
  /-- uid whose credentials were checked: the invoking user, or the target / root
  user with `targetpw` / `rootpw` -/
  authUid : Nat
  /-- `CLOCK_BOOTTIME` nanoseconds at successful authentication -/
  time : Nat
  /-- set by `sudo -k` -/
  disabled : Bool
  deriving DecidableEq, Repr, Inhabited

/-- Linux has no kernel tty tickets. Authentication uses sudo's
`ts_init_key_nonglobal`: `kernel` shares the tty scope, falling back to the
parent process only without a controlling terminal. -/
def scopeFor (t : TimestampType) (ttyDev : Option Nat) (sid sidStart ppid ppidStart : Nat) :
    Scope :=
  match t with
  | .tty | .kernel =>
    match ttyDev with
    | some d => .tty d sid sidStart
    | none => .ppid ppid ppidStart
  | .ppid => .ppid ppid ppidStart
  | .global => .global

theorem kernel_scope_tty (ttyDev : Nat) (sid sidStart ppid ppidStart : Nat) :
    scopeFor .kernel (some ttyDev) sid sidStart ppid ppidStart = .tty ttyDev sid sidStart := rfl

theorem kernel_scope_no_tty (sid sidStart ppid ppidStart : Nat) :
    scopeFor .kernel none sid sidStart ppid ppidStart = .ppid ppid ppidStart := rfl

/-- A kernel-mode ticket on another tty cannot authorize this request. -/
theorem kernel_scope_terminal_separation (tty₁ tty₂ sid sidStart ppid ppidStart : Nat)
    (h : tty₁ ≠ tty₂) :
    scopeFor .kernel (some tty₁) sid sidStart ppid ppidStart ≠
      scopeFor .kernel (some tty₂) sid sidStart ppid ppidStart := by
  simpa [scopeFor] using (fun eq => h (Scope.tty.inj eq).1 :
    Scope.tty tty₁ sid sidStart ≠ .tty tty₂ sid sidStart)

/-- Timeout in seconds (`none` = never expires, `some 0` = never cache) → nanoseconds check. -/
def fresh (now : Nat) (timeout : Option Nat) (time : Nat) : Bool :=
  match timeout with
  | none => true
  | some t => t != 0 && decide (now - time ≤ t * 10 ^ 9)

/-- A record grants authentication for `(scope, authUid)` at time `now`. -/
def valid (now : Nat) (timeout : Option Nat) (scope : Scope) (authUid : Nat) (r : Record) :
    Bool :=
  !r.disabled && decide (r.scope = scope) && decide (r.authUid = authUid) &&
    decide (r.time ≤ now) && fresh now timeout r.time

def lookup (now : Nat) (timeout : Option Nat) (scope : Scope) (authUid : Nat)
    (rs : List Record) : Bool :=
  rs.any (valid now timeout scope authUid)

/-- Upper bound on the number of records kept per file (most recent first). -/
def maxRecords : Nat := 128

/-- Record a successful authentication for `(scope, authUid)` at `now`: the fresh record
replaces any existing one for the same key and goes first; older records beyond
`maxRecords` are dropped. -/
def update (now : Nat) (scope : Scope) (authUid : Nat) (rs : List Record) : List Record :=
  { scope, authUid, time := now, disabled := false } ::
    (rs.filter (fun r => !(decide (r.scope = scope) && decide (r.authUid = authUid)))).take
      (maxRecords - 1)

/-- Bulk invalidation disables every record, independently of scope. -/
def invalidate (rs : List Record) : List Record :=
  rs.map fun r => { r with disabled := true }

/-- `sudo -k` disables all authentication identities in the selected scope. -/
def invalidateScope (scope : Scope) (rs : List Record) : List Record :=
  rs.map fun r => if r.scope = scope then { r with disabled := true } else r

/-! ## Encoding

`"LSTS" 0x01` magic/version, LEB128 record count, then the records. Each record is
a scope tag (0 tty, 1 ppid, 2 global) followed by its LEB128 fields, LEB128 `authUid`,
LEB128 `time`, and a disabled byte (0/1). Trailing garbage ⇒ decode failure. -/

def encNat (n : Nat) : List UInt8 :=
  if n < 128 then [UInt8.ofNat n] else UInt8.ofNat (n % 128 + 128) :: encNat (n / 128)
termination_by n
decreasing_by omega

def decNat : List UInt8 → Option (Nat × List UInt8)
  | [] => none
  | b :: bs =>
    if b.toNat < 128 then some (b.toNat, bs)
    else
      match decNat bs with
      | some (m, rest) => some (b.toNat - 128 + 128 * m, rest)
      | none => none

theorem decNat_encNat (n : Nat) (rest : List UInt8) :
    decNat (encNat n ++ rest) = some (n, rest) := by
  rw [encNat]
  split
  · rename_i h
    have h1 : n % 256 = n := by omega
    simp [decNat, h1, h]
  · have ih := decNat_encNat (n / 128) rest
    have h1 : (n % 128 + 128) % 256 = n % 128 + 128 := by omega
    have h2 : ¬(n % 128 + 128 < 128) := by omega
    simp only [decNat, List.cons_append, UInt8.toNat_ofNat', ih, h1, h2, ↓reduceIte,
      Option.some.injEq, Prod.mk.injEq, and_true]
    omega
termination_by n
decreasing_by omega

def encScope : Scope → List UInt8
  | .tty d s st => 0 :: encNat d ++ encNat s ++ encNat st
  | .ppid p st => 1 :: encNat p ++ encNat st
  | .global => [2]

def decScope : List UInt8 → Option (Scope × List UInt8)
  | [] => none
  | b :: bs =>
    if b = 0 then
      match decNat bs with
      | none => none
      | some (d, bs) =>
        match decNat bs with
        | none => none
        | some (s, bs) =>
          match decNat bs with
          | none => none
          | some (st, bs) => some (.tty d s st, bs)
    else if b = 1 then
      match decNat bs with
      | none => none
      | some (p, bs) =>
        match decNat bs with
        | none => none
        | some (st, bs) => some (.ppid p st, bs)
    else if b = 2 then some (.global, bs)
    else none

theorem decScope_encScope (s : Scope) (rest : List UInt8) :
    decScope (encScope s ++ rest) = some (s, rest) := by
  cases s <;> simp [encScope, decScope, decNat_encNat]

def encBool (b : Bool) : UInt8 := if b then 1 else 0

def encRecord (r : Record) : List UInt8 :=
  encScope r.scope ++ encNat r.authUid ++ encNat r.time ++ [encBool r.disabled]

def decRecord (bs : List UInt8) : Option (Record × List UInt8) :=
  match decScope bs with
  | none => none
  | some (scope, bs) =>
    match decNat bs with
    | none => none
    | some (authUid, bs) =>
      match decNat bs with
      | none => none
      | some (time, bs) =>
        match bs with
        | [] => none
        | b :: bs =>
          if b = 0 then some ({ scope, authUid, time, disabled := false }, bs)
          else if b = 1 then some ({ scope, authUid, time, disabled := true }, bs)
          else none

theorem decRecord_encRecord (r : Record) (rest : List UInt8) :
    decRecord (encRecord r ++ rest) = some (r, rest) := by
  obtain ⟨scope, authUid, time, disabled⟩ := r
  cases disabled <;> simp [encRecord, decRecord, encBool, decScope_encScope, decNat_encNat]

def encRecords : List Record → List UInt8
  | [] => []
  | r :: rs => encRecord r ++ encRecords rs

def decRecords : Nat → List UInt8 → Option (List Record × List UInt8)
  | 0, bs => some ([], bs)
  | k + 1, bs =>
    match decRecord bs with
    | none => none
    | some (r, bs) =>
      match decRecords k bs with
      | none => none
      | some (rs, bs) => some (r :: rs, bs)

theorem decRecords_encRecords (rs : List Record) (rest : List UInt8) :
    decRecords rs.length (encRecords rs ++ rest) = some (rs, rest) := by
  induction rs with
  | nil => simp [encRecords, decRecords]
  | cons r rs ih => simp [encRecords, decRecords, decRecord_encRecord, ih]

/-- `"LSTS"` + format version 1 -/
def magic : List UInt8 := [0x4C, 0x53, 0x54, 0x53, 0x01]

def encodeList (rs : List Record) : List UInt8 :=
  magic ++ encNat rs.length ++ encRecords rs

def decodeList (bs : List UInt8) : Option (List Record) :=
  if bs.take magic.length = magic then
    match decNat (bs.drop magic.length) with
    | none => none
    | some (n, bs) =>
      match decRecords n bs with
      | some (rs, []) => some rs
      | _ => none
  else none

theorem decodeList_encodeList (rs : List Record) : decodeList (encodeList rs) = some rs := by
  have h := decRecords_encRecords rs []
  simp only [List.append_nil] at h
  simp [decodeList, encodeList, decNat_encNat, h]

def encode (rs : List Record) : ByteArray := ⟨(encodeList rs).toArray⟩

/-- `none` on any malformed input; callers treat that as "no records". -/
def decode (b : ByteArray) : Option (List Record) := decodeList b.data.toList

/-- Records stored in a file's contents; unreadable contents ⇒ no records (fail closed). -/
def load (b : ByteArray) : List Record := (decode b).getD []

theorem decode_encode (rs : List Record) : decode (encode rs) = some rs := by
  simp [decode, encode, decodeList_encodeList]

theorem load_encode (rs : List Record) : load (encode rs) = rs := by
  simp [load, decode_encode]

/-! ## Properties -/

theorem valid_sound {now : Nat} {timeout : Option Nat} {scope : Scope} {authUid : Nat}
    {r : Record} (h : valid now timeout scope authUid r = true) :
    (r.scope = scope ∧ r.authUid = authUid ∧ r.time ≤ now ∧
      ∀ t, timeout = some t → now - r.time ≤ t * 10 ^ 9 ∧ t ≠ 0) ∧ ¬ r.disabled := by
  simp only [valid, fresh, Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hd, hs⟩, hu⟩, ht⟩, hf⟩ := h
  refine ⟨⟨hs, hu, ht, ?_⟩, by simp [hd]⟩
  intro t ht'
  subst ht'
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq] at hf
  exact ⟨hf.2, hf.1⟩

theorem lookup_iff {now : Nat} {timeout : Option Nat} {scope : Scope} {authUid : Nat}
    {rs : List Record} :
    lookup now timeout scope authUid rs = true ↔ ∃ r ∈ rs, valid now timeout scope authUid r = true := by
  simp [lookup]

/-- A successful lookup is witnessed by a record satisfying every validity condition. -/
theorem lookup_sound {now : Nat} {timeout : Option Nat} {scope : Scope} {authUid : Nat}
    {rs : List Record} (h : lookup now timeout scope authUid rs = true) :
    ∃ r ∈ rs, r.scope = scope ∧ r.authUid = authUid ∧ r.time ≤ now ∧ r.disabled = false ∧
      ∀ t, timeout = some t → now - r.time ≤ t * 10 ^ 9 ∧ t ≠ 0 := by
  obtain ⟨r, hr, hv⟩ := lookup_iff.mp h
  obtain ⟨⟨h1, h2, h3, h4⟩, h5⟩ := valid_sound hv
  exact ⟨r, hr, h1, h2, h3, by simpa using h5, h4⟩

@[simp] theorem lookup_nil (now : Nat) (timeout : Option Nat) (scope : Scope) (authUid : Nat) :
    lookup now timeout scope authUid [] = false := rfl

/-- `timestamp_timeout = 0`: nothing is ever cached. -/
theorem lookup_timeout_zero (now : Nat) (scope : Scope) (authUid : Nat) (rs : List Record) :
    lookup now (some 0) scope authUid rs = false := by
  simp [lookup, valid, fresh]

/-- After bulk invalidation no record is accepted. -/
theorem lookup_invalidate (now : Nat) (timeout : Option Nat) (scope : Scope) (authUid : Nat)
    (rs : List Record) : lookup now timeout scope authUid (invalidate rs) = false := by
  simp [lookup, invalidate, valid]

theorem lookup_invalidateScope (now : Nat) (timeout : Option Nat) (scope : Scope)
    (authUid : Nat) (rs : List Record) :
    lookup now timeout scope authUid (invalidateScope scope rs) = false := by
  simp only [lookup, invalidateScope, List.any_map]
  apply List.any_eq_false.mpr
  intro r _
  by_cases h : r.scope = scope <;> simp [h, valid]

theorem invalidateScope_other (scope : Scope) (r : Record) (h : r.scope ≠ scope) :
    invalidateScope scope [r] = [r] := by
  simp [invalidateScope, h]

theorem lookup_update_self (now t : Nat) (scope : Scope) (authUid : Nat) (rs : List Record)
    (ht : 0 < t) : lookup now (some t) scope authUid (update now scope authUid rs) = true := by
  simp [lookup, update, valid, fresh]
  omega

theorem lookup_update_self_none (now : Nat) (scope : Scope) (authUid : Nat) (rs : List Record) :
    lookup now none scope authUid (update now scope authUid rs) = true := by
  simp [lookup, update, valid, fresh]

/-- Isolation: updating `(scope, authUid)` never makes a record valid for a different key. -/
theorem lookup_update_other {now now' : Nat} {timeout : Option Nat} {scope scope' : Scope}
    {authUid authUid' : Nat} {rs : List Record} (hne : (scope', authUid') ≠ (scope, authUid))
    (h : lookup now timeout scope' authUid' (update now' scope authUid rs) = true) :
    lookup now timeout scope' authUid' rs = true := by
  rw [lookup_iff] at h ⊢
  obtain ⟨r, hr, hv⟩ := h
  simp only [update, List.mem_cons] at hr
  rcases hr with rfl | hr
  · obtain ⟨⟨h1, h2, -⟩, -⟩ := valid_sound hv
    simp at h1 h2
    exact absurd (by rw [h1, h2]) hne
  · exact ⟨r, (List.mem_filter.mp (List.mem_of_mem_take hr)).1, hv⟩

/-- Isolation: as long as the file is below its record limit, updating one key leaves
lookups for every other key unchanged. -/
theorem lookup_update_other_eq {now now' : Nat} {timeout : Option Nat} {scope scope' : Scope}
    {authUid authUid' : Nat} {rs : List Record} (hne : (scope', authUid') ≠ (scope, authUid))
    (hlen : rs.length < maxRecords) :
    lookup now timeout scope' authUid' (update now' scope authUid rs) =
      lookup now timeout scope' authUid' rs := by
  apply Bool.eq_iff_iff.mpr
  refine ⟨lookup_update_other hne, fun h => ?_⟩
  rw [lookup_iff] at h ⊢
  obtain ⟨r, hr, hv⟩ := h
  refine ⟨r, ?_, hv⟩
  obtain ⟨⟨h1, h2, -⟩, -⟩ := valid_sound hv
  have hlen' : (rs.filter (fun r => !(decide (r.scope = scope) && decide (r.authUid = authUid)))).length
      ≤ maxRecords - 1 := by
    have := List.length_filter_le (fun r => !(decide (r.scope = scope) && decide (r.authUid = authUid))) rs
    omega
  simp only [update, List.mem_cons, List.take_of_length_le hlen', List.mem_filter]
  right
  refine ⟨hr, ?_⟩
  simp only [h1, h2, Bool.not_eq_true', Bool.and_eq_false_iff, decide_eq_false_iff_not]
  by_cases hs : scope' = scope
  · subst hs; right; intro hu; exact hne (by rw [hu])
  · left; exact hs

/-- A future-dated record (e.g. from before a clock reset) is never accepted. -/
theorem valid_not_future {now : Nat} {timeout : Option Nat} {scope : Scope} {authUid : Nat}
    {r : Record} (h : now < r.time) : valid now timeout scope authUid r = false := by
  simp [valid]
  intros
  omega

/-! ## `/proc` parsing helpers (pure) -/

/-- Fields of `/proc/<pid>/stat` after the `comm` field. `comm` may contain spaces and
parentheses, so parsing starts after the *last* `)`. Field 3 (`state`) is index 0. -/
def statTailFields (bs : List UInt8) : Option (List String) :=
  let closeParen : UInt8 := 0x29
  match (bs.reverse.dropWhile (· != closeParen)) with
  | [] => none
  | _ :: revPrefix =>
    let tail := bs.drop (revPrefix.length + 1)
    let chunks := (tail.splitBy (fun a b => a != 0x20 && b != 0x20)).filter
      (fun c => !c.all (· == 0x20))
    some (chunks.map fun c => String.ofList (c.map fun b => Char.ofNat b.toNat))

/-- Numeric field `n` (1-based, as in `proc(5)`, `n ≥ 3`) of `/proc/<pid>/stat`. -/
def statField (bs : List UInt8) (n : Nat) : Option Nat := do
  let fs ← statTailFields bs
  let f ← fs[n - 3]?
  f.toNat?

/-- Convert the kernel's `tty_nr` encoding (`/proc/<pid>/stat` field 7) to a glibc
`dev_t` (`makedev(major, minor)`), i.e. the terminal's `st_rdev`. -/
def ttyNrToDev (n : Nat) : Nat :=
  let major := (n >>> 8) &&& 0xfff
  let minor := (n &&& 0xff) ||| ((n >>> 12) &&& 0xfff00)
  ((major &&& 0xfffff000) <<< 32) ||| ((major &&& 0xfff) <<< 8) |||
    ((minor &&& 0xffffff00) <<< 12) ||| (minor &&& 0xff)

end LeanSudo.Timestamp
