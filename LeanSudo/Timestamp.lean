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

/-- Scan by the on-disk size, not the number of recognized records. A short
header, size below the header width, truncated body, or malformed known entry
terminates scanning. Foreign versions/sizes/types are skipped without changing
subsequent offsets. -/
def scanFrom (bytes : ByteArray) (offset fuel : Nat) : List LocatedEntry :=
  match fuel with
  | 0 => []
  | fuel + 1 =>
    if offset + 4 > bytes.size then [] else
      let version := bytes[offset]!.toNat + 256 * bytes[offset + 1]!.toNat
      let size := bytes[offset + 2]!.toNat + 256 * bytes[offset + 3]!.toNat
      if size < 4 ∨ offset + size > bytes.size then [] else
        if version = 2 ∧ size = recordSize then
          let kind := bytes[offset + 4]!.toNat + 256 * bytes[offset + 5]!.toNat
          if 1 ≤ kind ∧ kind ≤ 4 then
            match decodeEntry (bytes.extract offset (offset + size)) with
            | some e => ⟨offset, e⟩ :: scanFrom bytes (offset + size) fuel
            | none => []
          else scanFrom bytes (offset + size) fuel
        else scanFrom bytes (offset + size) fuel

def scan (bytes : ByteArray) : List LocatedEntry := scanFrom bytes 0 (bytes.size / 4)

def DiskEntry.forSession (e : DiskEntry) (sid : Nat) : Option Record :=
  if e.kind = 1 ∨ e.sid = sid then e.toRecord else none

def loadFor (sid : Nat) (bytes : ByteArray) : List Record :=
  (scan bytes).filterMap fun located => located.entry.forSession sid

theorem DiskEntry.forSession_sound {e : DiskEntry} {sid : Nat} {r : Record}
    (h : e.forSession sid = some r) : e.kind = 1 ∨ e.sid = sid := by
  unfold DiskEntry.forSession at h
  split at h
  · assumption
  · contradiction

theorem DiskEntry.forSession_wrong_sid (e : DiskEntry) (sid : Nat)
    (hg : e.kind ≠ 1) (hs : e.sid ≠ sid) : e.forSession sid = none := by
  simp [DiskEntry.forSession, hg, hs]

/-- Every runtime-projected record comes from a real scanned slot and is
global or belongs to the requesting session. -/
theorem loadFor_sound {sid : Nat} {bytes : ByteArray} {r : Record}
    (h : r ∈ loadFor sid bytes) :
    ∃ located ∈ scan bytes, located.entry.toRecord = some r ∧
      (located.entry.kind = 1 ∨ located.entry.sid = sid) := by
  obtain ⟨located, hm, hp⟩ := List.mem_filterMap.mp h
  have hs := DiskEntry.forSession_sound hp
  exact ⟨located, hm, by simpa [DiskEntry.forSession, hs] using hp, hs⟩

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
