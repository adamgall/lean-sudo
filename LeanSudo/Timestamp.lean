import LeanSudo.Policy.Types

namespace LeanSudo.Timestamp

inductive Scope where
  | tty (dev : Nat) (sid : Nat) (sidStart : Nat)
  | ppid (pid : Nat) (start : Nat)
  | global
  deriving DecidableEq, Repr, Inhabited

structure Record where
  scope : Scope
  authUid : Nat
  time : Nat
  disabled : Bool
  deriving DecidableEq, Repr, Inhabited

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

theorem kernel_scope_terminal_separation (tty₁ tty₂ sid sidStart ppid ppidStart : Nat)
    (h : tty₁ ≠ tty₂) :
    scopeFor .kernel (some tty₁) sid sidStart ppid ppidStart ≠
      scopeFor .kernel (some tty₂) sid sidStart ppid ppidStart := by
  simpa [scopeFor] using (fun eq => h (Scope.tty.inj eq).1 :
    Scope.tty tty₁ sid sidStart ≠ .tty tty₂ sid sidStart)

def fresh (now : Nat) (timeout : Option Nat) (time : Nat) : Bool :=
  match timeout with
  | none => true
  | some t => t != 0 && decide (now - time < t * 10 ^ 9)

def valid (now : Nat) (timeout : Option Nat) (scope : Scope) (authUid : Nat) (r : Record) :
    Bool :=
  !r.disabled && decide (r.scope = scope) && decide (r.authUid = authUid) &&
    decide (r.time ≤ now) && fresh now timeout r.time

def lookup (now : Nat) (timeout : Option Nat) (scope : Scope) (authUid : Nat)
    (rs : List Record) : Bool :=
  rs.any (valid now timeout scope authUid)

def recordSize : Nat := 56

structure DiskEntry where
  kind : Nat
  flags : Nat
  authUid : Nat
  sid : Nat
  start : Nat
  time : Nat
  key : Nat
  deriving DecidableEq, Repr, Inhabited

structure LocatedEntry where
  offset : Nat
  entry : DiskEntry
  startValid : Bool := true
  timeValid : Bool := true
  deriving DecidableEq, Repr, Inhabited

def lockEntry : DiskEntry := ⟨4, 0, 0, 0, 0, 0, 0⟩

def DiskEntry.ofRecord (sid : Nat) (r : Record) : DiskEntry :=
  let flags := if r.disabled then 1 else 0
  match r.scope with
  | .global => ⟨1, flags, r.authUid, sid, 0, r.time, 0⟩
  | .tty dev session start => ⟨2, flags, r.authUid, session, start, r.time, dev⟩
  | .ppid pid start => ⟨3, flags, r.authUid, sid, start, r.time, pid⟩

def DiskEntry.toRecord (e : DiskEntry) : Option Record := do
  let scope ← match e.kind with
    | 1 => some Scope.global
    | 2 => some (.tty e.key e.sid e.start)
    | 3 => some (.ppid e.key e.start)
    | _ => none
  return { scope, authUid := e.authUid, time := e.time, disabled := e.flags % 2 == 1 }

def disabledEntry (entry : DiskEntry) : DiskEntry :=
  { entry with flags := entry.flags / 2 * 2 + 1 }

theorem disabledEntry_upper_flags (entry : DiskEntry) :
    (disabledEntry entry).flags / 2 = entry.flags / 2 := by
  simp only [disabledEntry]
  omega

theorem disabledEntry_low_flag (entry : DiskEntry) :
    (disabledEntry entry).flags % 2 = 1 := by
  simp [disabledEntry, Nat.add_mod]

theorem DiskEntry.toRecord_disabled {entry : DiskEntry} {record : Record}
    (h : entry.toRecord = some record) :
    record.disabled = (entry.flags % 2 == 1) := by
  unfold DiskEntry.toRecord at h
  split at h <;> simp_all
  all_goals cases h; rfl

theorem disabledEntry_toRecord_disabled {entry : DiskEntry} {record : Record}
    (h : (disabledEntry entry).toRecord = some record) : record.disabled = true := by
  simpa [disabledEntry_low_flag] using DiskEntry.toRecord_disabled h

def DiskEntry.matches (e : DiskEntry) (scope : Scope) (authUid : Nat)
    (anyUid : Bool := false) : Bool :=
  (anyUid || e.authUid == authUid) &&
    match scope with
    | .global => e.kind == 1
    | .tty dev _ start => e.kind == 2 && e.key == dev && e.start == start
    | .ppid pid start => e.kind == 3 && e.key == pid && e.start == start

theorem disabledEntry_matches (entry : DiskEntry) (scope : Scope) (uid : Nat)
    (anyUid : Bool) :
    (disabledEntry entry).matches scope uid anyUid = entry.matches scope uid anyUid := rfl

theorem DiskEntry.toRecord_ofRecord (sid : Nat) (r : Record) :
    (DiskEntry.ofRecord sid r).toRecord = some r := by
  obtain ⟨scope, uid, time, disabled⟩ := r
  cases scope <;> cases disabled <;> rfl

theorem DiskEntry.matches_uid {e : DiskEntry} {scope : Scope} {uid : Nat}
    (h : e.matches scope uid false = true) : e.authUid = uid := by
  simp only [DiskEntry.matches, Bool.false_or, Bool.and_eq_true, beq_iff_eq] at h
  exact h.1

theorem DiskEntry.matches_tty_start {e : DiskEntry} {dev sid start uid : Nat}
    {anyUid : Bool} (h : e.matches (.tty dev sid start) uid anyUid = true) :
    e.kind = 2 ∧ e.key = dev ∧ e.start = start := by
  simp_all [DiskEntry.matches]

theorem DiskEntry.matches_ppid_start {e : DiskEntry} {pid start uid : Nat}
    {anyUid : Bool} (h : e.matches (.ppid pid start) uid anyUid = true) :
    e.kind = 3 ∧ e.key = pid ∧ e.start = start := by
  simp_all [DiskEntry.matches]

theorem DiskEntry.matches_ofRecord (sid : Nat) (r : Record) :
    (DiskEntry.ofRecord sid r).matches r.scope r.authUid = true := by
  obtain ⟨scope, uid, time, disabled⟩ := r
  cases scope <;> simp [DiskEntry.ofRecord, DiskEntry.matches]

theorem DiskEntry.matches_tty_sid_independent (e : DiskEntry)
    (dev sid₁ sid₂ start uid : Nat) (anyUid : Bool) :
    e.matches (.tty dev sid₁ start) uid anyUid =
      e.matches (.tty dev sid₂ start) uid anyUid := rfl

def entryFor (lockScope : Scope) (sid : Nat) (record : Record) : DiskEntry :=
  let entry := DiskEntry.ofRecord sid record
  if record.scope = .global then
    match lockScope with
    | .tty dev _ start => { entry with start, key := dev }
    | .ppid pid start => { entry with start, key := pid }
    | .global => entry
  else entry

def updateEntry (scope lockScope : Scope) (sid authUid : Nat) (record : Record) :
    Option DiskEntry :=
  if record.scope = scope ∧ record.authUid = authUid then
    some (entryFor lockScope sid record)
  else none

theorem entryFor_projection (lockScope : Scope) (sid : Nat) (record : Record) :
    (entryFor lockScope sid record).toRecord = some record := by
  obtain ⟨scope, uid, time, disabled⟩ := record
  cases scope <;> cases lockScope <;> cases disabled <;>
    simp [entryFor, DiskEntry.ofRecord, DiskEntry.toRecord]

theorem entryFor_matches (lockScope : Scope) (sid : Nat) (record : Record) :
    (entryFor lockScope sid record).matches record.scope record.authUid = true := by
  obtain ⟨scope, uid, time, disabled⟩ := record
  cases scope <;> cases lockScope <;>
    simp [entryFor, DiskEntry.ofRecord, DiskEntry.matches]

theorem updateEntry_sound {scope lockScope : Scope} {sid uid : Nat}
    {record : Record} {entry : DiskEntry}
    (h : updateEntry scope lockScope sid uid record = some entry) :
    record.scope = scope ∧ record.authUid = uid ∧
      entry.toRecord = some record ∧ entry.matches scope uid = true := by
  unfold updateEntry at h
  split at h
  · rename_i hk
    have he := Option.some.inj h
    subst entry
    exact ⟨hk.1, hk.2, entryFor_projection _ _ _,
      by simpa [← hk.1, ← hk.2] using entryFor_matches lockScope sid record⟩
  · contradiction

theorem updateEntry_wrong_uid (scope lockScope : Scope) (sid uid : Nat) (record : Record)
    (h : record.authUid ≠ uid) : updateEntry scope lockScope sid uid record = none := by
  simp [updateEntry, h]

theorem updateEntry_wrong_scope (scope lockScope : Scope) (sid uid : Nat) (record : Record)
    (h : record.scope ≠ scope) : updateEntry scope lockScope sid uid record = none := by
  simp [updateEntry, h]

def encNat : Nat → Nat → List UInt8
  | 0, _ => []
  | width + 1, n => UInt8.ofNat (n % 256) :: encNat width (n / 256)

def decNat : Nat → List UInt8 → Option (Nat × List UInt8)
  | 0, bs => some (0, bs)
  | _ + 1, [] => none
  | width + 1, b :: bs => do
    let (n, rest) ← decNat width bs
    return (b.toNat + 256 * n, rest)

@[simp] theorem length_encNat (width n : Nat) : (encNat width n).length = width := by
  induction width generalizing n with
  | zero => rfl
  | succ w ih => simp [encNat, ih]

theorem decNat_encNat (width n : Nat) (rest : List UInt8)
    (h : n < 256 ^ width) :
    decNat width (encNat width n ++ rest) = some (n, rest) := by
  induction width generalizing n with
  | zero =>
    have : n = 0 := by simpa using h
    subst n
    rfl
  | succ w ih =>
    have hn : n / 256 < 256 ^ w := by
      apply (Nat.div_lt_iff_lt_mul (by decide : 0 < 256)).2
      simpa [Nat.pow_succ, Nat.mul_comm] using h
    have hm : (n % 256) % 256 = n % 256 := Nat.mod_eq_of_lt (Nat.mod_lt _ (by decide))
    simp [encNat, decNat, ih _ hn, UInt8.toNat_ofNat', hm, Nat.mod_add_div]

def encTime (n : Nat) : List UInt8 :=
  encNat 8 (n / 1000000000) ++ encNat 8 (n % 1000000000)

def decTime (bs : List UInt8) : Option (Nat × List UInt8) := do
  let (seconds, bs) ← decNat 8 bs
  let (nanos, bs) ← decNat 8 bs
  if seconds < 2 ^ 63 ∧ nanos < 1000000000 then
    some (nanos + 1000000000 * seconds, bs)
  else none

theorem decTime_encTime (n : Nat) (rest : List UInt8)
    (h : n / 1000000000 < 2 ^ 63) :
    decTime (encTime n ++ rest) = some (n, rest) := by
  have hs : n / 1000000000 < 256 ^ 8 := by omega
  have hn : n % 1000000000 < 1000000000 := Nat.mod_lt _ (by decide)
  have hn' : n % 1000000000 < 256 ^ 8 := by omega
  simp [encTime, decTime, List.append_assoc, decNat_encNat _ _ _ hs,
    decNat_encNat _ _ _ hn', h, hn, Nat.mod_add_div]

def DiskEntry.Representable (e : DiskEntry) : Prop :=
  e.kind < 256 ^ 2 ∧ e.flags < 256 ^ 2 ∧ e.authUid < 256 ^ 4 ∧
  e.sid < 2 ^ 31 ∧ e.start / 1000000000 < 2 ^ 63 ∧
  e.time / 1000000000 < 2 ^ 63 ∧ e.key < 256 ^ 8 ∧
  (e.kind = 3 → e.key < 2 ^ 31)

instance (e : DiskEntry) : Decidable e.Representable := inferInstanceAs
  (Decidable (e.kind < 256 ^ 2 ∧ e.flags < 256 ^ 2 ∧ e.authUid < 256 ^ 4 ∧
    e.sid < 2 ^ 31 ∧ e.start / 1000000000 < 2 ^ 63 ∧
    e.time / 1000000000 < 2 ^ 63 ∧ e.key < 256 ^ 8 ∧
    (e.kind = 3 → e.key < 2 ^ 31)))

def encEntry (e : DiskEntry) : List UInt8 :=
  encNat 2 2 ++ encNat 2 recordSize ++ encNat 2 e.kind ++ encNat 2 e.flags ++
  encNat 4 e.authUid ++ encNat 4 e.sid ++ encTime e.start ++ encTime e.time ++
  encNat 8 e.key

def decEntry (bs : List UInt8) : Option (DiskEntry × List UInt8) := do
  let (version, bs) ← decNat 2 bs
  let (size, bs) ← decNat 2 bs
  if version ≠ 2 ∨ size ≠ recordSize then none else do
    let (kind, bs) ← decNat 2 bs
    let (flags, bs) ← decNat 2 bs
    let (authUid, bs) ← decNat 4 bs
    let (sid, bs) ← decNat 4 bs
    let (start, bs) ← decTime bs
    let (time, bs) ← decTime bs
    let (rawKey, bs) ← decNat 8 bs
    let key := if kind = 3 then rawKey % 256 ^ 4 else rawKey
    let e : DiskEntry := ⟨kind, flags, authUid, sid, start, time, key⟩
    if e.Representable then some (e, bs) else none

@[simp] theorem length_encEntry (e : DiskEntry) : (encEntry e).length = recordSize := by
  simp [encEntry, encTime, recordSize]

theorem decEntry_encEntry (e : DiskEntry) (rest : List UInt8) (h : e.Representable) :
    decEntry (encEntry e ++ rest) = some (e, rest) := by
  rcases h with ⟨hk, hf, hu, hs, hst, ht, hkey, hp⟩
  have hs' : e.sid < 256 ^ 4 := by omega
  have he : e.Representable := ⟨hk, hf, hu, hs, hst, ht, hkey, hp⟩
  have hnorm : (if e.kind = 3 then e.key % 256 ^ 4 else e.key) = e.key := by
    by_cases hk3 : e.kind = 3
    · have hpid := hp hk3
      have hsmall : e.key < 256 ^ 4 := by omega
      simp [hk3, Nat.mod_eq_of_lt hsmall]
    · simp [hk3]
  simp [encEntry, List.append_assoc, decEntry,
    decNat_encNat 2 2 _ (by decide),
    decNat_encNat 2 recordSize _ (by decide),
    decNat_encNat 2 e.kind _ hk, decNat_encNat 2 e.flags _ hf,
    decNat_encNat 4 e.authUid _ hu, decNat_encNat 4 e.sid _ hs',
    decTime_encTime e.start _ hst, decTime_encTime e.time _ ht,
    decNat_encNat 8 e.key _ hkey, hnorm, he]

def encodeEntry (e : DiskEntry) : ByteArray := ⟨(encEntry e).toArray⟩

def decodeEntry (bytes : ByteArray) : Option DiskEntry :=
  match decEntry bytes.data.toList with
  | some (e, []) => some e
  | _ => none

theorem decodeEntry_encodeEntry (e : DiskEntry) (h : e.Representable) :
    decodeEntry (encodeEntry e) = some e := by
  have hd := decEntry_encEntry e [] h
  simp only [List.append_nil] at hd
  simp [decodeEntry, encodeEntry, hd]

def slotWord (bytes : ByteArray) (offset : Nat) : Nat → Nat
  | 0 => 0
  | width + 1 => bytes[offset]!.toNat + 256 * slotWord bytes (offset + 1) width

def decodeSlot (bytes : ByteArray) (offset : Nat := 0) : Option LocatedEntry :=
  if bytes.size = recordSize ∧ slotWord bytes 0 2 = 2 ∧
      slotWord bytes 2 2 = recordSize then
    let kind := slotWord bytes 4 2
    if 1 ≤ kind ∧ kind ≤ 4 then
      let startSeconds := slotWord bytes 16 8
      let startNanos := slotWord bytes 24 8
      let timeSeconds := slotWord bytes 32 8
      let timeNanos := slotWord bytes 40 8
      some {
        offset
        entry := {
          kind, flags := slotWord bytes 6 2, authUid := slotWord bytes 8 4
          sid := slotWord bytes 12 4
          start := startNanos + 1000000000 * startSeconds
          time := timeNanos + 1000000000 * timeSeconds
          key := slotWord bytes 48 (if kind = 3 then 4 else 8) }
        startValid := decide (startSeconds < 2 ^ 63 ∧ startNanos < 1000000000)
        timeValid := decide (timeSeconds < 2 ^ 63 ∧ timeNanos < 1000000000) }
    else none
  else none

theorem decodeSlot_validity {bytes : ByteArray} {offset : Nat} {located : LocatedEntry}
    (h : decodeSlot bytes offset = some located) :
    located.offset = offset ∧
      (located.startValid = true ↔
        slotWord bytes 16 8 < 2 ^ 63 ∧ slotWord bytes 24 8 < 1000000000) ∧
      (located.timeValid = true ↔
        slotWord bytes 32 8 < 2 ^ 63 ∧ slotWord bytes 40 8 < 1000000000) := by
  dsimp only [decodeSlot] at h
  split at h
  · split at h
    · cases Option.some.inj h
      simp
    · contradiction
  · contradiction

def DiskEntry.forSession (e : DiskEntry) (sid : Nat) : Option Record :=
  if e.kind = 1 ∨ e.sid = sid then e.toRecord else none

def LocatedEntry.matches (located : LocatedEntry) (scope : Scope) (authUid : Nat)
    (anyUid : Bool := false) : Bool :=
  (decide (scope = .global) || located.startValid) &&
    located.entry.matches scope authUid anyUid

def LocatedEntry.forSession (located : LocatedEntry) (sid : Nat) : Option Record :=
  if located.startValid && located.timeValid then located.entry.forSession sid else none

def LocatedEntry.recordFor (located : LocatedEntry) (scope : Scope) (authUid sid : Nat) :
    Option Record :=
  if located.matches scope authUid then located.forSession sid else none

theorem DiskEntry.forSession_sound {e : DiskEntry} {sid : Nat} {r : Record}
    (h : e.forSession sid = some r) : e.kind = 1 ∨ e.sid = sid := by
  unfold DiskEntry.forSession at h
  split at h
  · assumption
  · contradiction

theorem DiskEntry.forSession_wrong_sid (e : DiskEntry) (sid : Nat)
    (hg : e.kind ≠ 1) (hs : e.sid ≠ sid) : e.forSession sid = none := by
  simp [DiskEntry.forSession, hg, hs]

theorem LocatedEntry.matches_uid {located : LocatedEntry} {scope : Scope} {uid : Nat}
    (h : located.matches scope uid = true) : located.entry.authUid = uid := by
  simp only [LocatedEntry.matches, Bool.and_eq_true] at h
  exact DiskEntry.matches_uid h.2

theorem LocatedEntry.matches_tty_start {located : LocatedEntry} {dev sid start uid : Nat}
    {anyUid : Bool} (h : located.matches (.tty dev sid start) uid anyUid = true) :
    located.startValid = true ∧ located.entry.kind = 2 ∧
      located.entry.key = dev ∧ located.entry.start = start := by
  simp_all [LocatedEntry.matches, DiskEntry.matches]

theorem LocatedEntry.matches_ppid_start {located : LocatedEntry} {pid start uid : Nat}
    {anyUid : Bool} (h : located.matches (.ppid pid start) uid anyUid = true) :
    located.startValid = true ∧ located.entry.kind = 3 ∧
      located.entry.key = pid ∧ located.entry.start = start := by
  simp_all [LocatedEntry.matches, DiskEntry.matches]

theorem LocatedEntry.forSession_sound {located : LocatedEntry} {sid : Nat} {r : Record}
    (h : located.forSession sid = some r) :
    located.startValid = true ∧ located.timeValid = true ∧
      located.entry.toRecord = some r ∧
      (located.entry.kind = 1 ∨ located.entry.sid = sid) := by
  unfold LocatedEntry.forSession at h
  split at h
  · rename_i hv
    have hs := DiskEntry.forSession_sound h
    simp only [Bool.and_eq_true] at hv
    exact ⟨hv.1, hv.2,
      by simpa [DiskEntry.forSession, hs] using h, hs⟩
  · contradiction

theorem LocatedEntry.recordFor_sound {located : LocatedEntry} {scope : Scope}
    {uid sid : Nat} {r : Record} (h : located.recordFor scope uid sid = some r) :
    located.entry.authUid = uid ∧ located.matches scope uid = true ∧
      located.startValid = true ∧ located.timeValid = true ∧
      located.entry.toRecord = some r ∧
      (located.entry.kind = 1 ∨ located.entry.sid = sid) := by
  unfold LocatedEntry.recordFor at h
  split at h
  · rename_i hm
    exact ⟨LocatedEntry.matches_uid hm, hm, LocatedEntry.forSession_sound h⟩
  · contradiction

theorem LocatedEntry.recordFor_invalid_start (located : LocatedEntry)
    (scope : Scope) (uid sid : Nat) (h : located.startValid = false) :
    located.recordFor scope uid sid = none := by
  simp [LocatedEntry.recordFor, LocatedEntry.forSession, h]

theorem LocatedEntry.recordFor_invalid_time (located : LocatedEntry)
    (scope : Scope) (uid sid : Nat) (h : located.timeValid = false) :
    located.recordFor scope uid sid = none := by
  simp [LocatedEntry.recordFor, LocatedEntry.forSession, h]

theorem LocatedEntry.recordFor_wrong_sid (located : LocatedEntry)
    (scope : Scope) (uid sid : Nat) (hg : located.entry.kind ≠ 1)
    (hs : located.entry.sid ≠ sid) : located.recordFor scope uid sid = none := by
  simp [LocatedEntry.recordFor, LocatedEntry.forSession, DiskEntry.forSession, hg, hs]

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
  exact ⟨Nat.le_of_lt hf.2, hf.1⟩

theorem valid_timeout_strict {now timeout : Nat} {scope : Scope} {authUid : Nat}
    {r : Record} (h : valid now (some timeout) scope authUid r = true) :
    now - r.time < timeout * 10 ^ 9 := by
  simp only [valid, fresh, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.2.2

theorem LocatedEntry.authorized_sound {located : LocatedEntry} {scope : Scope}
    {uid sid now : Nat} {timeout : Option Nat} {r : Record}
    (hr : located.recordFor scope uid sid = some r)
    (hv : valid now timeout scope uid r = true) :
    located.entry.authUid = uid ∧ located.matches scope uid = true ∧
      located.startValid = true ∧ located.timeValid = true ∧
      (located.entry.kind = 1 ∨ located.entry.sid = sid) ∧
      r.scope = scope ∧ r.authUid = uid ∧ r.disabled = false ∧ r.time ≤ now ∧
      ∀ t, timeout = some t → t ≠ 0 ∧ now - r.time < t * 10 ^ 9 := by
  have hs := LocatedEntry.recordFor_sound hr
  have ht := valid_sound hv
  refine ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2.2,
    ht.1.1, ht.1.2.1, by simpa using ht.2, ht.1.2.2.1, ?_⟩
  intro t he
  exact ⟨(ht.1.2.2.2 t he).2, valid_timeout_strict (by simpa [he] using hv)⟩

theorem LocatedEntry.disabled_not_valid (located : LocatedEntry) (scope : Scope)
    (uid sid now : Nat) (timeout : Option Nat) {record : Record}
    (h : (LocatedEntry.recordFor { located with entry := disabledEntry located.entry }
      scope uid sid) = some record) : valid now timeout scope uid record = false := by
  have hs := LocatedEntry.recordFor_sound h
  have hd := disabledEntry_toRecord_disabled hs.2.2.2.2.1
  simp [valid, hd]

theorem lookup_iff {now : Nat} {timeout : Option Nat} {scope : Scope} {authUid : Nat}
    {rs : List Record} :
    lookup now timeout scope authUid rs = true ↔ ∃ r ∈ rs, valid now timeout scope authUid r = true := by
  simp [lookup]

theorem lookup_sound {now : Nat} {timeout : Option Nat} {scope : Scope} {authUid : Nat}
    {rs : List Record} (h : lookup now timeout scope authUid rs = true) :
    ∃ r ∈ rs, r.scope = scope ∧ r.authUid = authUid ∧ r.time ≤ now ∧ r.disabled = false ∧
      ∀ t, timeout = some t → now - r.time ≤ t * 10 ^ 9 ∧ t ≠ 0 := by
  obtain ⟨r, hr, hv⟩ := lookup_iff.mp h
  obtain ⟨⟨h1, h2, h3, h4⟩, h5⟩ := valid_sound hv
  exact ⟨r, hr, h1, h2, h3, by simpa using h5, h4⟩

@[simp] theorem lookup_nil (now : Nat) (timeout : Option Nat) (scope : Scope) (authUid : Nat) :
    lookup now timeout scope authUid [] = false := rfl

theorem lookup_timeout_zero (now : Nat) (scope : Scope) (authUid : Nat) (rs : List Record) :
    lookup now (some 0) scope authUid rs = false := by
  simp [lookup, valid, fresh]

theorem lookup_invalidateScope (located : LocatedEntry) (scope : Scope)
    (uid sid now : Nat) (timeout : Option Nat) {record : Record}
    (h : (LocatedEntry.recordFor { located with entry := disabledEntry located.entry }
      scope uid sid) = some record) : valid now timeout scope uid record = false :=
  located.disabled_not_valid scope uid sid now timeout h

theorem invalidateScope_other (located : LocatedEntry) (scope : Scope)
    (h : located.matches scope 0 true = false) :
    (if located.matches scope 0 true then disabledEntry located.entry else located.entry) =
      located.entry := by simp [h]

theorem lookup_update_other {scope lockScope other : Scope} {sid uid otherUid now : Nat}
    {timeout : Option Nat} {record : Record} {entry : DiskEntry}
    (hw : updateEntry scope lockScope sid uid record = some entry)
    (hne : (other, otherUid) ≠ (scope, uid)) :
    valid now timeout other otherUid record = false := by
  have hs := updateEntry_sound hw
  cases hv : valid now timeout other otherUid record with
  | false => rfl
  | true =>
    have hv := valid_sound hv
    exact False.elim (hne (Prod.ext (hv.1.1.symm.trans hs.1)
      (hv.1.2.1.symm.trans hs.2.1)))

theorem decode_encode (entry : DiskEntry) (h : entry.Representable) :
    decodeEntry (encodeEntry entry) = some entry :=
  decodeEntry_encodeEntry entry h

theorem valid_not_future {now : Nat} {timeout : Option Nat} {scope : Scope} {authUid : Nat}
    {r : Record} (h : now < r.time) : valid now timeout scope authUid r = false := by
  simp [valid]
  intros
  omega

def statTailFields (bs : List UInt8) : Option (List String) :=
  let closeParen : UInt8 := 0x29
  match (bs.reverse.dropWhile (· != closeParen)) with
  | [] => none
  | _ :: revPrefix =>
    let tail := bs.drop (revPrefix.length + 1)
    let chunks := (tail.splitBy (fun a b => a != 0x20 && b != 0x20)).filter
      (fun c => !c.all (· == 0x20))
    some (chunks.map fun c => String.ofList (c.map fun b => Char.ofNat b.toNat))

def statField (bs : List UInt8) (n : Nat) : Option Nat := do
  let fs ← statTailFields bs
  let f ← fs[n - 3]?
  f.toNat?

def ttyNrToDev (n : Nat) : Nat :=
  let major := (n >>> 8) &&& 0xfff
  let minor := (n &&& 0xff) ||| ((n >>> 12) &&& 0xfff00)
  ((major &&& 0xfffff000) <<< 32) ||| ((major &&& 0xfff) <<< 8) |||
    ((minor &&& 0xffffff00) <<< 12) ||| (minor &&& 0xff)

end LeanSudo.Timestamp
