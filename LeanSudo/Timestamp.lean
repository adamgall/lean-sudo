import LeanSudo.Policy.Types

/-!
# Timestamp records (pure)

Pure model of sudo's credential cache ("timestamp") file: record identity (scope),
validity, update / invalidation, and a canonical codec with a proved roundtrip.
Runtime uses the bounded `scanStep` raw-slot decoder, `LocatedEntry.recordFor`,
and `updateEntry`; their theorems cover the same helpers consumed by IO.
Raw slot matching preserves malformed first matches, while authorization rejects
invalid timespecs (including global start times). All IO lives in `LeanSudo.Sys.Timestamp`.

Times are `CLOCK_BOOTTIME` nanoseconds; timeouts are seconds (as in sudoers).
-/

namespace LeanSudo.Timestamp

/-- What a cached credential is bound to (sudo's `timestamp_type`). Start times
(nanoseconds since boot, converted from `/proc/<pid>/stat`) guard against pid reuse. -/
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
  | some t => t != 0 && decide (now - time < t * 10 ^ 9)

/-- A record grants authentication for `(scope, authUid)` at time `now`. -/
def valid (now : Nat) (timeout : Option Nat) (scope : Scope) (authUid : Nat) (r : Record) :
    Bool :=
  !r.disabled && decide (r.scope = scope) && decide (r.authUid = authUid) &&
    decide (r.time ≤ now) && fresh now timeout r.time

def lookup (now : Nat) (timeout : Option Nat) (scope : Scope) (authUid : Nat)
    (rs : List Record) : Bool :=
  rs.any (valid now timeout scope authUid)

/-- Bound for pure snapshot updates. Disk transactions update fixed slots instead
of truncating or reordering the shared sudo timestamp file. -/
def maxRecords : Nat := 128

/-- Update an in-memory snapshot after successful authentication: the fresh record
replaces the same key and goes first; older snapshot records beyond `maxRecords`
are dropped. The IO layer writes only the selected on-disk slot. -/
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

/-! ## Ubuntu64 sudo timestamp v2

The wire layout is sudo 1.9.17p2's little-endian `timestamp_entry`: four
16-bit header fields, uid and sid (32 bits), two 64-bit seconds/nanoseconds
pairs, and the 64-bit ttydev/ppid union. There is no file-level count or magic.
The first entry is the exclusive-allocation lock. Runtime scans retain byte
offsets, including across foreign records, and never compact a locked file.
-/

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
  /-- Raw timespec validity is separate from slot identity. -/
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

/-- Set only TS_DISABLED. The quotient preserves every higher flag bit; runtime
invalidation writes only these two flag bytes, never re-encodes a raw slot. -/
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

/-- Slot identity deliberately ignores SID and disabled status, just like
`ts_match_record`. SID is checked separately before authorizing a ticket.
`anyUid` belongs to the search key, never to the stored entry's flags. -/
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
  simp only [DiskEntry.matches, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.2.1.1, h.2.1.2, h.2.2⟩

theorem DiskEntry.matches_ppid_start {e : DiskEntry} {pid start uid : Nat}
    {anyUid : Bool} (h : e.matches (.ppid pid start) uid anyUid = true) :
    e.kind = 3 ∧ e.key = pid ∧ e.start = start := by
  simp only [DiskEntry.matches, Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.2.1.1, h.2.1.2, h.2.2⟩

theorem DiskEntry.matches_ofRecord (sid : Nat) (r : Record) :
    (DiskEntry.ofRecord sid r).matches r.scope r.authUid = true := by
  obtain ⟨scope, uid, time, disabled⟩ := r
  cases scope <;> simp [DiskEntry.ofRecord, DiskEntry.matches]

theorem DiskEntry.matches_tty_sid_independent (e : DiskEntry)
    (dev sid₁ sid₂ start uid : Nat) (anyUid : Bool) :
    e.matches (.tty dev sid₁ start) uid anyUid =
      e.matches (.tty dev sid₂ start) uid anyUid := rfl

/-- Runtime slot construction retains sudo's nonglobal lock identity in the
unused fields of a global record. -/
def entryFor (lockScope : Scope) (sid : Nat) (record : Record) : DiskEntry :=
  let entry := DiskEntry.ofRecord sid record
  if record.scope = .global then
    match lockScope with
    | .tty dev _ start => { entry with start, key := dev }
    | .ppid pid start => { entry with start, key := pid }
    | .global => entry
  else entry

/-- Only the authenticated identity and scope of the locked ticket may be written.
The IO layer additionally checks `Representable` before encoding. -/
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

/-- Fixed-width little-endian words; values outside the width are truncated.
Roundtrip theorems explicitly require representability. -/
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

/-- Bounds of the actual C scalar types, including signed pid_t/time_t. -/
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
    -- pid_t occupies only the low four bytes; the union's high bytes are padding.
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

/-- Read at most eight bytes directly, without allocating lists for runtime slots. -/
def slotWord (bytes : ByteArray) (offset : Nat) : Nat → Nat
  | 0 => 0
  | width + 1 => bytes[offset]!.toNat + 256 * slotWord bytes (offset + 1) width

/-- Raw v2 decoder: signed SID bits and invalid timespecs still identify a slot.
Unlike the canonical codec, this must not reject a slot before matching it. -/
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

/-- A model record is representable iff its canonical disk projection is. -/
def Record.Representable (r : Record) : Prop := (DiskEntry.ofRecord 0 r).Representable

def encRecord (r : Record) : List UInt8 := encEntry (DiskEntry.ofRecord 0 r)

def decRecord (bs : List UInt8) : Option (Record × List UInt8) := do
  let (entry, rest) ← decEntry bs
  let record ← entry.toRecord
  return (record, rest)

theorem decRecord_encRecord (r : Record) (rest : List UInt8) (h : r.Representable) :
    decRecord (encRecord r ++ rest) = some (r, rest) := by
  simp [encRecord, decRecord, decEntry_encEntry _ _ h, DiskEntry.toRecord_ofRecord]

/-- Scope helpers use an ordinary v2 record with zero uid/time/flags. -/
def encScope (s : Scope) : List UInt8 := encRecord ⟨s, 0, 0, false⟩

def decScope (bs : List UInt8) : Option (Scope × List UInt8) := do
  let (record, rest) ← decRecord bs
  return (record.scope, rest)

theorem decScope_encScope (s : Scope) (rest : List UInt8)
    (h : (Record.mk s 0 0 false).Representable) :
    decScope (encScope s ++ rest) = some (s, rest) := by
  simp [encScope, decScope, decRecord_encRecord _ _ h]

def encRecords : List Record → List UInt8
  | [] => []
  | r :: rs => encRecord r ++ encRecords rs

def decRecords : Nat → List UInt8 → Option (List Record × List UInt8)
  | 0, bs => some ([], bs)
  | k + 1, bs => do
    let (r, bs) ← decRecord bs
    let (rs, bs) ← decRecords k bs
    return (r :: rs, bs)

theorem decRecords_encRecords (rs : List Record) (rest : List UInt8)
    (h : ∀ r ∈ rs, r.Representable) :
    decRecords rs.length (encRecords rs ++ rest) = some (rs, rest) := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    have hr := h r (by simp)
    have hrs : ∀ r ∈ rs, r.Representable := fun r hm => h r (by simp [hm])
    simp [encRecords, decRecords, List.append_assoc, decRecord_encRecord _ _ hr, ih hrs]

@[simp] theorem length_encRecords (rs : List Record) :
    (encRecords rs).length = rs.length * recordSize := by
  induction rs with
  | nil => rfl
  | cons r rs ih => simp [encRecords, encRecord, ih, Nat.add_mul, Nat.add_comm]

def encodeList (rs : List Record) : List UInt8 :=
  encEntry lockEntry ++ encRecords rs

/-- Strict whole-file codec for the pure model. Runtime uses `scan` instead so
foreign entries remain in place and do not invalidate unrelated tickets. -/
def decodeList (bs : List UInt8) : Option (List Record) := do
  let (lock, bs) ← decEntry bs
  if lock.kind ≠ 4 then none else
    match decRecords (bs.length / recordSize) bs with
    | some (rs, []) => some rs
    | _ => none

theorem decodeList_encodeList (rs : List Record)
    (h : ∀ r ∈ rs, r.Representable) : decodeList (encodeList rs) = some rs := by
  have hd := decRecords_encRecords rs [] h
  simp only [List.append_nil] at hd
  unfold decodeList encodeList
  rw [decEntry_encEntry lockEntry (encRecords rs) (by decide)]
  simp [lockEntry, recordSize, hd]

def encode (rs : List Record) : ByteArray := ⟨(encodeList rs).toArray⟩

def decode (b : ByteArray) : Option (List Record) := decodeList b.data.toList

def load (b : ByteArray) : List Record := (decode b).getD []

theorem decode_encode (rs : List Record) (h : ∀ r ∈ rs, r.Representable) :
    decode (encode rs) = some rs := by
  simp [decode, encode, decodeList_encodeList _ h]

theorem load_encode (rs : List Record) (h : ∀ r ∈ rs, r.Representable) :
    load (encode rs) = rs := by
  simp [load, decode_encode _ h]

/-- A bounded chunk is relative to `offset`, while `extent` is the absolute file end.
Foreign records need only their header; a v2/56 slot requires an exact 56-byte window.
No SID or timespec error terminates the structural scan. -/
inductive ScanStep where
  | stop
  | next (offset : Nat) (entry : Option LocatedEntry)
  deriving DecidableEq, Repr, Inhabited

def scanStep (bytes : ByteArray) (offset extent : Nat) : ScanStep :=
  if bytes.size < 4 then .stop else
    let version := slotWord bytes 0 2
    let size := slotWord bytes 2 2
    if size < 4 ∨ offset + size > extent then .stop else
      if version = 2 ∧ size = recordSize then
        if bytes.size ≠ recordSize then .stop else
          .next (offset + size) (decodeSlot bytes offset)
      else .next (offset + size) none

theorem scanStep_bounds {bytes : ByteArray} {offset extent next : Nat}
    {entry : Option LocatedEntry} (h : scanStep bytes offset extent = .next next entry) :
    offset + 4 ≤ next ∧ next ≤ extent := by
  dsimp only [scanStep] at h
  split at h
  · contradiction
  · split at h
    · contradiction
    · rename_i hb
      split at h
      · split at h
        · contradiction
        · cases h
          omega
      · cases h
        omega

theorem scanStep_decoded {bytes : ByteArray} {offset extent next : Nat}
    {entry : LocatedEntry} (h : scanStep bytes offset extent = .next next (some entry)) :
    decodeSlot bytes offset = some entry := by
  dsimp only [scanStep] at h
  split at h
  · contradiction
  · split at h
    · contradiction
    · split at h
      · split at h
        · contradiction
        · exact (ScanStep.next.inj h).2
      · cases h

/-- Tail accumulation preserves physical order, including malformed matching
slots. In particular a rejected first match cannot expose a later duplicate. -/
def scanAcc (bytes : ByteArray) (offset fuel : Nat) (acc : List LocatedEntry) :
    List LocatedEntry :=
  match fuel with
  | 0 => acc.reverse
  | fuel + 1 =>
    match scanStep (bytes.extract offset (offset + recordSize)) offset bytes.size with
    | .stop => acc.reverse
    | .next next entry =>
      scanAcc bytes next fuel (match entry with | some e => e :: acc | none => acc)

def scanFrom (bytes : ByteArray) (offset fuel : Nat) : List LocatedEntry :=
  scanAcc bytes offset fuel []

def scan (bytes : ByteArray) : List LocatedEntry := scanFrom bytes 0 (bytes.size / 4)

theorem scanAcc_append (bytes : ByteArray) (offset fuel : Nat)
    (front suffix : List LocatedEntry) :
    scanAcc bytes offset fuel (front ++ suffix) =
      suffix.reverse ++ scanAcc bytes offset fuel front := by
  induction fuel generalizing offset front with
  | zero => simp [scanAcc, List.reverse_append]
  | succ fuel ih =>
    cases hs : scanStep (bytes.extract offset (offset + recordSize)) offset bytes.size with
    | stop => simp [scanAcc, hs, List.reverse_append]
    | next next found =>
      cases found with
      | none => simpa only [scanAcc, hs] using ih next front
      | some entry =>
        simpa only [scanAcc, hs, List.cons_append] using ih next (entry :: front)

/-- Recognition prepends the physical first slot, even if it cannot authorize. -/
theorem scanFrom_next_some {bytes : ByteArray} {offset next fuel : Nat}
    {entry : LocatedEntry}
    (h : scanStep (bytes.extract offset (offset + recordSize)) offset bytes.size =
      .next next (some entry)) :
    scanFrom bytes offset (fuel + 1) = entry :: scanFrom bytes next fuel := by
  simpa [scanFrom, scanAcc, h] using scanAcc_append bytes next fuel [] [entry]

theorem scanFrom_next_none {bytes : ByteArray} {offset next fuel : Nat}
    (h : scanStep (bytes.extract offset (offset + recordSize)) offset bytes.size =
      .next next none) :
    scanFrom bytes offset (fuel + 1) = scanFrom bytes next fuel := by
  simp only [scanFrom, scanAcc, h]

/-- Every accumulated result originates in an actual bounded scanner step. -/
theorem scanAcc_origin (bytes : ByteArray) (offset fuel : Nat) (acc : List LocatedEntry)
    (entry : LocatedEntry) (h : entry ∈ scanAcc bytes offset fuel acc) :
    entry ∈ acc ∨ ∃ pos next,
      scanStep (bytes.extract pos (pos + recordSize)) pos bytes.size =
        .next next (some entry) := by
  induction fuel generalizing offset acc with
  | zero =>
    left
    simpa [scanAcc] using h
  | succ fuel ih =>
    cases hs : scanStep (bytes.extract offset (offset + recordSize)) offset bytes.size with
    | stop =>
      left
      simpa [scanAcc, hs] using h
    | next next found =>
      cases found with
      | none =>
        exact ih next acc (by simpa [scanAcc, hs] using h)
      | some located =>
        have hr := ih next (located :: acc) (by simpa [scanAcc, hs] using h)
        rcases hr with hm | hw
        · rcases List.mem_cons.mp hm with he | hm
          · subst entry
            exact Or.inr ⟨offset, next, hs⟩
          · exact Or.inl hm
        · exact Or.inr hw

theorem scan_sound {bytes : ByteArray} {entry : LocatedEntry} (h : entry ∈ scan bytes) :
    ∃ pos next,
      scanStep (bytes.extract pos (pos + recordSize)) pos bytes.size =
        .next next (some entry) ∧ pos + 4 ≤ next ∧ next ≤ bytes.size := by
  have ho := scanAcc_origin bytes 0 (bytes.size / 4) [] entry h
  rcases ho with hm | ⟨pos, next, hs⟩
  · cases hm
  · exact ⟨pos, next, hs, scanStep_bounds hs⟩

/-- A scanned slot's validity flags describe the raw bytes, not a normalized
timestamp reconstructed by the encoder. -/
theorem scan_timespecs {bytes : ByteArray} {entry : LocatedEntry}
    (h : entry ∈ scan bytes) :
    ∃ chunk, decodeSlot chunk entry.offset = some entry ∧
      (entry.startValid = true ↔
        slotWord chunk 16 8 < 2 ^ 63 ∧ slotWord chunk 24 8 < 1000000000) ∧
      (entry.timeValid = true ↔
        slotWord chunk 32 8 < 2 ^ 63 ∧ slotWord chunk 40 8 < 1000000000) := by
  obtain ⟨pos, next, hs, _⟩ := scan_sound h
  have hd := scanStep_decoded hs
  have hv := decodeSlot_validity hd
  exact ⟨_, by simpa [hv.1] using hd, hv.2⟩

def DiskEntry.forSession (e : DiskEntry) (sid : Nat) : Option Record :=
  if e.kind = 1 ∨ e.sid = sid then e.toRecord else none

/-- Identity matching precedes validity checks. A malformed nonglobal start
cannot equal a normalized process-incarnation key; global identity ignores it. -/
def LocatedEntry.matches (located : LocatedEntry) (scope : Scope) (authUid : Nat)
    (anyUid : Bool := false) : Bool :=
  (decide (scope = .global) || located.startValid) &&
    located.entry.matches scope authUid anyUid

/-- sudo's status check validates both timespecs, even for global entries. -/
def LocatedEntry.forSession (located : LocatedEntry) (sid : Nat) : Option Record :=
  if located.startValid && located.timeValid then located.entry.forSession sid else none

def LocatedEntry.recordFor (located : LocatedEntry) (scope : Scope) (authUid sid : Nat) :
    Option Record :=
  if located.matches scope authUid then located.forSession sid else none

def loadFor (sid : Nat) (bytes : ByteArray) : List Record :=
  (scan bytes).filterMap fun located => located.forSession sid

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
  simp only [LocatedEntry.matches, Bool.and_eq_true] at h
  exact ⟨by simpa using h.1, DiskEntry.matches_tty_start h.2⟩

theorem LocatedEntry.matches_ppid_start {located : LocatedEntry} {pid start uid : Nat}
    {anyUid : Bool} (h : located.matches (.ppid pid start) uid anyUid = true) :
    located.startValid = true ∧ located.entry.kind = 3 ∧
      located.entry.key = pid ∧ located.entry.start = start := by
  simp only [LocatedEntry.matches, Bool.and_eq_true] at h
  exact ⟨by simpa using h.1, DiskEntry.matches_ppid_start h.2⟩

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

/-- Every runtime-projected record comes from a real scanned slot and is
global or belongs to the requesting session. -/
theorem loadFor_sound {sid : Nat} {bytes : ByteArray} {r : Record}
    (h : r ∈ loadFor sid bytes) :
    ∃ located ∈ scan bytes, located.entry.toRecord = some r ∧
      (located.entry.kind = 1 ∨ located.entry.sid = sid) := by
  obtain ⟨located, hm, hp⟩ := List.mem_filterMap.mp h
  have hs := LocatedEntry.forSession_sound hp
  exact ⟨located, hm, hs.2.2.1, hs.2.2.2⟩

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
  exact ⟨Nat.le_of_lt hf.2, hf.1⟩

/-- Finite tickets expire at the exact deadline, not one nanosecond later. -/
theorem valid_timeout_strict {now timeout : Nat} {scope : Scope} {authUid : Nat}
    {r : Record} (h : valid now (some timeout) scope authUid r = true) :
    now - r.time < timeout * 10 ^ 9 := by
  simp only [valid, fresh, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.2.2

/-- Runtime authorization connects the selected raw slot to credential identity,
process/session binding, valid wire timespecs, and the disabled/future/expiry
checks. It does not reason about an obsolete in-memory update path. -/
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
