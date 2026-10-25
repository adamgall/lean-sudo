import Std

/-!
# sudo log-server protobuf bodies

Pure implementation of sudo v1.9.17p2 `lib/logsrv/log_server.proto`:
https://github.com/sudo-project/sudo/blob/v1.9.17p2/lib/logsrv/log_server.proto

The transport, not this module, adds the four-byte network-order frame length.
Signed values use protobuf int64/int32 (two's complement, **not** zigzag).
The public Int API normalizes values to the schema width. Window dimensions must
be nonnegative int32 values and stream indices must be in 0..4; an unrepresentable
window or stream encodes as an empty, hence rejected, message. Decoding validates
UTF-8, field numbers, lengths, varint overflow and wire types. Deprecated group
wire types are rejected, as in protobuf-c. Unknown supported fields are skipped.
Scalar fields have proto3 defaults; repeated numbers accept packed/unpacked forms.

General roundtrip proofs cover bounded varints, signed scalar normalization,
arbitrary UTF-8 and binary envelopes, TimeSpec, ClientHello, and the server
commit/log-id/error/abort families. Additional finite-family proofs cover I/O
stream routing and capability flags. There is no claimed universal roundtrip
theorem for all ClientMessage/ServerMessage values.
-/

namespace LeanSudo.LogSrv

structure TimeSpec where
  seconds : Int
  nanoseconds : Int
  deriving DecidableEq, Repr, Inhabited

inductive InfoValue where
  | number (value : Int)
  | string (value : String)
  | strings (values : List String)
  | numbers (values : List Int)
  deriving DecidableEq, Repr, Inhabited

structure InfoMessage where
  key : String
  value : InfoValue
  deriving DecidableEq, Repr, Inhabited

inductive ClientMessage where
  | hello (clientId : String)
  | accept (time : TimeSpec) (info : List InfoMessage) (expectIo : Bool)
  | reject (time : TimeSpec) (reason : String) (info : List InfoMessage)
  | exit (runtime : TimeSpec) (exitValue : Int) (dumpedCore : Bool)
      (signal : String) (error : String)
  | restart (logId : String) (resume : TimeSpec)
  | alert (time : TimeSpec) (reason : String) (info : List InfoMessage)
  | io (stream : Nat) (delay : TimeSpec) (data : ByteArray)
  | winsize (delay : TimeSpec) (rows : Nat) (cols : Nat)
  | suspend (delay : TimeSpec) (signal : String)
  deriving DecidableEq, Inhabited

structure ServerHello where
  serverId : String
  redirect : String
  servers : List String
  subcommands : Bool
  deriving DecidableEq, Repr, Inhabited

inductive ServerMessage where
  | hello (value : ServerHello)
  | commit (time : TimeSpec)
  | logId (value : String)
  | error (value : String)
  | abort (value : String)
  deriving DecidableEq, Repr, Inhabited

namespace Wire

/-- Unsigned protobuf base-128 representation. -/
def encNat (n : Nat) : List UInt8 :=
  if n < 128 then [UInt8.ofNat n]
  else UInt8.ofNat (n % 128 + 128) :: encNat (n / 128)
termination_by n
decreasing_by omega

/-- Mathematical varint decoder; the wire entry point bounds it to ten bytes. -/
def decNat : List UInt8 → Option (Nat × List UInt8)
  | [] => none
  | b :: bs =>
    if b.toNat < 128 then some (b.toNat, bs)
    else
      match decNat bs with
      | some (n, rest) => some (b.toNat - 128 + 128 * n, rest)
      | none => none

/-- Varint roundtrip preserves an arbitrary following byte sequence. -/
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

theorem encNat_length_le (n k : Nat) (positive : 0 < k) (bound : n < 128 ^ k) :
    (encNat n).length ≤ k := by
  induction k generalizing n with
  | zero => omega
  | succ k ih =>
    rw [encNat]
    split
    · simp
    · rename_i large
      have positive' : 0 < k := by
        by_cases h : k = 0
        · subst k
          simp at bound
          omega
        · omega
      have bound' : n / 128 < 128 ^ k := by
        rw [Nat.pow_succ] at bound
        omega
      simpa using Nat.succ_le_succ (ih (n / 128) positive' bound')

theorem encNat_length_uint64 (n : Nat) (bound : n < 2 ^ 64) :
    (encNat n).length ≤ 10 :=
  encNat_length_le n 10 (by decide) (by omega)

/-- List-facing bounded varint primitive; `varintAt` uses the same ten-byte
`decNat` primitive directly on a bounded byte-array window. -/
def varint (bs : List UInt8) : Option (Nat × List UInt8) := do
  let (n, rest) ← decNat (bs.take 10)
  if n < 2 ^ 64 then pure (n, rest ++ bs.drop 10) else none

/-- The overflow-checking list primitive preserves arbitrary trailing bytes for
every uint64 whose canonical representation fits the ten-byte limit. -/
theorem varint_encNat (n : Nat) (rest : List UInt8)
    (bound : n < 2 ^ 64) (width : (encNat n).length ≤ 10) :
    varint (encNat n ++ rest) = some (n, rest) := by
  simp [varint, List.take_append, List.take_of_length_le width, decNat_encNat,
    bound, List.drop_append, List.drop_eq_nil_of_le width]

/-- Every bounded uint64 roundtrips through the bounded wire parser. -/
theorem varint_uint64 (n : Nat) (rest : List UInt8) (bound : n < 2 ^ 64) :
    varint (encNat n ++ rest) = some (n, rest) :=
  varint_encNat n rest bound (encNat_length_uint64 n bound)

/-- Interpret the low `bits` bits as a signed integer. -/
def signed (bits : Nat) (n : Nat) : Int :=
  let n := n % 2 ^ bits
  if n < 2 ^ (bits - 1) then Int.ofNat n else Int.ofNat n - Int.ofNat (2 ^ bits)

/-- Negative int32 values are sign-extended to 64 bits before varint encoding. -/
def unsigned (bits : Nat) (n : Int) : Nat :=
  let n := signed bits (n % Int.ofNat (2 ^ bits)).toNat
  (n % Int.ofNat (2 ^ 64)).toNat

theorem unsigned_bound (bits : Nat) (n : Int) : unsigned bits n < 2 ^ 64 := by
  change (signed bits (n % Int.ofNat (2 ^ bits)).toNat % 18446744073709551616).toNat <
    18446744073709551616
  omega

theorem signed_unsigned64 (n : Int) (lo : -(2 ^ 63) ≤ n) (hi : n < 2 ^ 63) :
    signed 64 (unsigned 64 n) = n := by
  simp [unsigned, signed]
  split <;> split <;> omega

theorem signed_unsigned32 (n : Int) (lo : -(2 ^ 31) ≤ n) (hi : n < 2 ^ 31) :
    signed 32 (unsigned 32 n) = n := by
  simp [unsigned, signed]
  split <;> split <;> omega

inductive Value where
  | number (n : Nat)
  | bytes (bs : List UInt8)
  | skipped
  deriving DecidableEq, Repr

abbrev Field := Nat × Value

/-- A bounded window, never a conversion of the remaining frame to a list. -/
def window (bs : ByteArray) (pos count : Nat) : List UInt8 :=
  (bs.extract pos (pos + count)).data.toList

@[simp] theorem window_eq (bs : ByteArray) (pos count : Nat) :
    window bs pos count = (bs.data.toList.drop pos).take count := by
  simp [window]

/-- Only the next ten bytes can be inspected by the varint primitive. Its
non-tail recursion therefore has a fixed bound independent of the frame. -/
def varintAt (bs : ByteArray) (pos : Nat) : Option (Nat × Nat) := do
  let input := window bs pos 10
  let (n, rest) ← decNat input
  if n < 2 ^ 64 then pure (n, pos + (input.length - rest.length)) else none

theorem varintAt_encNat (bs : ByteArray) (pos n : Nat) (rest : List UInt8)
    (suffix : bs.data.toList.drop pos = encNat n ++ rest) (bound : n < 2 ^ 64) :
    varintAt bs pos = some (n, pos + (encNat n).length) := by
  have width := encNat_length_uint64 n bound
  simp [varintAt, suffix, List.take_append, List.take_of_length_le width,
    decNat_encNat, bound]

/-- Flat wire scanning: each successful step advances a byte index and appends
one field to an array. There is no group stack, suffix-length scan, or non-tail
field call. Fuel bounds the loop by the frame size; the cursor guard enforces
actual progress. The accumulated array is converted to a list only once. -/
def fieldsAux (bs : ByteArray) : Nat → Nat → Array Field → Option (List Field)
  | 0, _, _ => none
  | fuel + 1, pos, acc =>
    if pos = bs.size then some acc.toList else do
      let (key, start) ← varintAt bs pos
      let number := key / 8
      let kind := key % 8
      if number = 0 ∨ number ≥ 2 ^ 29 then none else do
        let (value, next) ←
          if kind = 0 then do
            let (n, next) ← varintAt bs start
            pure (Value.number n, next)
          else if kind = 1 then
            if start + 8 ≤ bs.size then pure (Value.skipped, start + 8) else none
          else if kind = 2 then do
            let (size, payload) ← varintAt bs start
            if payload + size ≤ bs.size then
              pure (Value.bytes (window bs payload size), payload + size)
            else none
          else if kind = 5 then
            if start + 4 ≤ bs.size then pure (Value.skipped, start + 4) else none
          else none
        if pos < next ∧ next ≤ bs.size then
          fieldsAux bs fuel next (acc.push (number, value))
        else none

def fieldsArray (bs : ByteArray) : Option (List Field) :=
  fieldsAux bs (bs.size + 1) 0 #[]

/-- List-facing convenience API, using exactly the same indexed decoder. -/
def fields (bs : List UInt8) : Option (List Field) :=
  fieldsArray ⟨bs.toArray⟩

@[simp] theorem fieldsArray_toArray (bs : List UInt8) :
    fieldsArray ⟨bs.toArray⟩ = fields bs := rfl

/-- Group start and end tags are rejected without parsing any following fields.
This is a theorem about the actual scanning loop, for every cursor and suffix. -/
theorem fieldsAux_reject_group (bs : ByteArray) (fuel pos key next : Nat)
    (acc : Array Field) (notEnd : pos ≠ bs.size)
    (keyParsed : varintAt bs pos = some (key, next))
    (group : key % 8 = 3 ∨ key % 8 = 4) :
    fieldsAux bs (fuel + 1) pos acc = none := by
  rcases group with group | group <;>
    simp [fieldsAux, notEnd, keyParsed, group]

/-- The varint window has a frame-independent maximum length. -/
theorem varint_window_bounded (bs : ByteArray) (pos : Nat) :
    (window bs pos 10).length ≤ 10 := by
  simpa only [window_eq, List.length_take] using
    Nat.min_le_left 10 (bs.data.toList.drop pos).length

def number (tag n : Nat) : List UInt8 := encNat (tag * 8) ++ encNat n

def bytes (tag : Nat) (bs : List UInt8) : List UInt8 :=
  encNat (tag * 8 + 2) ++ encNat bs.length ++ bs

def text (tag : Nat) (s : String) : List UInt8 := bytes tag s.toUTF8.data.toList

def values (tag : Nat) (fs : List Field) : List Value :=
  fs.filterMap fun (n, v) => if n = tag then some v else none

def asNumber : Value → Option Nat
  | .number n => some n
  | _ => none

def asBytes : Value → Option (List UInt8)
  | .bytes bs => some bs
  | _ => none

def asString (v : Value) : Option String := do
  let bs ← asBytes v
  String.fromUTF8? ⟨bs.toArray⟩

/-- String fields preserve every valid Unicode string, including embedded NUL. -/
theorem asString_utf8 (s : String) :
    asString (.bytes s.toUTF8.data.toList) = some s := by
  simp [asString, asBytes, String.toUTF8, String.fromUTF8?, String.fromUTF8, s.isValidUTF8]

def getNumber (tag : Nat) (fs : List Field) : Option Nat := do
  let ns ← (values tag fs).mapM asNumber
  pure (ns.getLast?.getD 0)

def getString (tag : Nat) (fs : List Field) : Option String := do
  let ss ← (values tag fs).mapM asString
  pure (ss.getLast?.getD "")

/-- Repeated occurrences of a singular embedded message merge in wire order. -/
def getMessage (tag : Nat) (fs : List Field) : Option (List Field) := do
  let chunks ← (values tag fs).mapM asBytes
  fields chunks.flatten

def getData (tag : Nat) (fs : List Field) : Option ByteArray := do
  let chunks ← (values tag fs).mapM asBytes
  pure ⟨(chunks.getLast?.getD []).toArray⟩

/-- Select a oneof, merging successive occurrences of the same embedded-message
case. Unknown fields do not reset a oneof. Strings and numeric cases replace.
Chunks are prepended and flattened once, never appended to a growing prefix. -/
def oneof (known merge : Nat → Bool) (fs : List Field) : Option Field := do
  let (selected, chunks) ← fs.foldl (fun selected f =>
    if !known f.1 then selected
    else
      let fresh := match f.2 with
        | .bytes bs => (f, [bs])
        | _ => (f, [])
      match selected, f.2 with
      | some ((tag, .bytes _), chunks), .bytes next =>
        if tag = f.1 ∧ merge tag then some (f, next :: chunks) else some fresh
      | _, _ => some fresh) (none : Option (Field × List (List UInt8)))
  match selected.2 with
  | .bytes _ => pure (selected.1, .bytes chunks.reverse.flatten)
  | _ => pure selected

/-- Validate every known occurrence before decoding the selected oneof case. -/
@[inline] def decodeOneof (known merge : Nat → Bool) (dec : Field → Option α)
    (fs : List Field) : Option α := do
  for f in fs do
    if known f.1 then let _ ← dec f; pure ()
  dec (← oneof known merge fs)

/-- Reading a canonical one-byte key advances the cursor by exactly one. -/
theorem varintAt_small (bs : ByteArray) (pos n : Nat) (rest : List UInt8)
    (suffix : bs.data.toList.drop pos = UInt8.ofNat n :: rest) (small : n < 128) :
    varintAt bs pos = some (n, pos + 1) := by
  have encoded : encNat n = [UInt8.ofNat n] := by simp [encNat, small]
  have parsed := varintAt_encNat bs pos n rest (by simpa [encoded] using suffix) (by omega)
  simpa [encoded] using parsed

private theorem fieldsAux_key_prefix (bs : ByteArray) (pos key : Nat) (rest : List UInt8)
    (suffix : bs.data.toList.drop pos = UInt8.ofNat key :: rest)
    (inBounds : pos ≤ bs.size) (small : key < 128) :
    pos < bs.size ∧ pos + 1 + rest.length = bs.size ∧
      varintAt bs pos = some (key, pos + 1) ∧ bs.data.toList.drop (pos + 1) = rest := by
  have size := congrArg List.length suffix
  simp only [List.length_drop, Array.length_toList, ByteArray.size_data,
    List.length_cons] at size
  refine ⟨by omega, by omega, varintAt_small bs pos key rest suffix small, ?_⟩
  rw [← List.drop_drop]
  simp [suffix]

private theorem fieldsAux_bytes_small (bs : ByteArray) (fuel pos tag : Nat)
    (payload : List UInt8) (acc : Array Field)
    (suffix : bs.data.toList.drop pos =
      UInt8.ofNat (tag * 8 + 2) :: encNat payload.length ++ payload)
    (inBounds : pos ≤ bs.size) (positive : 0 < tag) (small : tag < 16)
    (bound : payload.length < 2 ^ 64) :
    fieldsAux bs (fuel + 2) pos acc = some (acc.push (tag, .bytes payload)).toList := by
  obtain ⟨progress, endPos, keyParsed, afterKey⟩ :=
    fieldsAux_key_prefix bs pos _ _ suffix inBounds (by omega)
  have sizeParsed := varintAt_encNat bs (pos + 1) payload.length payload afterKey bound
  change pos + 1 + (encNat payload.length ++ payload).length = bs.size at endPos
  simp only [List.length_append, ← Nat.add_assoc] at endPos
  have afterSize : bs.data.toList.drop (pos + 1 + (encNat payload.length).length) =
      payload := by
    rw [← List.drop_drop, afterKey]
    simp
  simp [fieldsAux, Nat.ne_of_lt progress, keyParsed, sizeParsed, afterSize, endPos, progress,
    show (tag * 8 + 2) / 8 = tag by omega,
    show (tag * 8 + 2) % 8 = 2 by omega] <;> omega

/-- The numeric-field step consumes its key and varint before its sole tail call. -/
theorem fieldsAux_number_step (bs : ByteArray) (fuel pos tag n : Nat)
    (rest : List UInt8) (acc : Array Field)
    (suffix : bs.data.toList.drop pos = UInt8.ofNat (tag * 8) :: encNat n ++ rest)
    (inBounds : pos ≤ bs.size) (positive : 0 < tag) (small : tag < 16)
    (bound : n < 2 ^ 64) :
    fieldsAux bs (fuel + 1) pos acc =
      fieldsAux bs fuel (pos + 1 + (encNat n).length) (acc.push (tag, .number n)) := by
  obtain ⟨notEnd, size, keyParsed, afterKey⟩ :=
    fieldsAux_key_prefix bs pos _ _ suffix inBounds (by omega)
  have valueParsed := varintAt_encNat bs (pos + 1) n rest afterKey bound
  change pos + 1 + (encNat n ++ rest).length = bs.size at size
  simp only [List.length_append] at size
  have progress : pos < pos + 1 + (encNat n).length ∧
      pos + 1 + (encNat n).length ≤ bs.size := by omega
  simp [fieldsAux, Nat.ne_of_lt notEnd, keyParsed, valueParsed, progress,
    show (tag * 8) / 8 = tag by omega, show (tag * 8) % 8 = 0 by omega] <;> omega

/-- Every log-server embedded-message tag preserves an arbitrary bounded binary
payload through the complete field parser, not just the varint primitives. -/
theorem fields_bytes_roundtrip (tag : Nat) (payload : List UInt8)
    (positive : 0 < tag) (small : tag < 16) (bound : payload.length < 2 ^ 64) :
    fields (bytes tag payload) = some [(tag, .bytes payload)] := by
  have keySmall : tag * 8 + 2 < 128 := by omega
  have keyEncoded : encNat (tag * 8 + 2) = [UInt8.ofNat (tag * 8 + 2)] := by
    rw [encNat, ite_eq_left keySmall]
  have encoded : bytes tag payload =
      UInt8.ofNat (tag * 8 + 2) :: encNat payload.length ++ payload := by
    simp only [bytes, keyEncoded, List.cons_append, List.nil_append]
  rw [encoded]
  have size : (UInt8.ofNat (tag * 8 + 2) :: encNat payload.length ++ payload).length + 1 =
      ((encNat payload.length).length + payload.length) + 2 := by
    simp only [List.length_cons, List.length_append]
    omega
  unfold fields fieldsArray
  simp only [ByteArray.size, List.size_toArray, size]
  exact fieldsAux_bytes_small _ _ 0 tag payload #[] (by simp)
    (by omega) positive small bound

end Wire

private def encTime (t : TimeSpec) : List UInt8 :=
  Wire.number 1 (Wire.unsigned 64 t.seconds) ++ Wire.number 2 (Wire.unsigned 32 t.nanoseconds)

private def decTime (fs : List Wire.Field) : Option TimeSpec := do
  let seconds ← Wire.getNumber 1 fs
  let nanoseconds ← Wire.getNumber 2 fs
  pure ⟨Wire.signed 64 seconds, Wire.signed 32 nanoseconds⟩

private theorem decTime_fields (a b : Nat) :
    decTime [(1, .number a), (2, .number b)] =
      some ⟨Wire.signed 64 a, Wire.signed 32 b⟩ := by
  simp [decTime, Wire.getNumber, Wire.values, Wire.asNumber]

private theorem fields_time (a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    Wire.fields (Wire.number 1 a ++ Wire.number 2 b) =
      some [(1, .number a), (2, .number b)] := by
  have encoded : Wire.number 1 a ++ Wire.number 2 b =
      8 :: Wire.encNat a ++ 16 :: Wire.encNat b := by
    change (Wire.encNat 8 ++ Wire.encNat a) ++ (Wire.encNat 16 ++ Wire.encNat b) = _
    rw [show Wire.encNat 8 = [8] by decide +kernel,
      show Wire.encNat 16 = [16] by decide +kernel]
    rfl
  rw [encoded]
  let bs : ByteArray := ⟨(8 :: Wire.encNat a ++ 16 :: Wire.encNat b).toArray⟩
  have size : bs.size = (Wire.encNat a).length + (Wire.encNat b).length + 2 := by
    simp [bs, ByteArray.size]
    omega
  have first := Wire.fieldsAux_number_step bs
    ((Wire.encNat a).length + (Wire.encNat b).length + 2) 0 1 a
    (16 :: Wire.encNat b) #[] (by simp [bs]) (by omega) (by decide) (by decide) ha
  have second := Wire.fieldsAux_number_step bs
    ((Wire.encNat a).length + (Wire.encNat b).length + 1)
    (0 + 1 + (Wire.encNat a).length) 2 b [] (#[].push (1, .number a))
    (by
      have offset : 0 + 1 + (Wire.encNat a).length = (Wire.encNat a).length + 1 := by omega
      simp [bs, offset])
    (by omega) (by decide) (by decide) hb
  change Wire.fieldsAux bs (bs.size + 1) 0 #[] = _
  rw [size, first, second]
  have endPos : 0 + 1 + (Wire.encNat a).length + 1 + (Wire.encNat b).length =
      bs.size := by omega
  simp [Wire.fieldsAux, endPos]

/-- All representable POSIX time values roundtrip through protobuf's numeric
field parser, including the negative int32 sign-extension case. -/
theorem time_roundtrip (t : TimeSpec)
    (slo : -(2 ^ 63) ≤ t.seconds) (shi : t.seconds < 2 ^ 63)
    (nlo : -(2 ^ 31) ≤ t.nanoseconds) (nhi : t.nanoseconds < 2 ^ 31) :
    (Wire.fields (encTime t)).bind decTime = some t := by
  have parsed := fields_time (Wire.unsigned 64 t.seconds) (Wire.unsigned 32 t.nanoseconds)
    (Wire.unsigned_bound 64 t.seconds) (Wire.unsigned_bound 32 t.nanoseconds)
  have decoded := decTime_fields (Wire.unsigned 64 t.seconds) (Wire.unsigned 32 t.nanoseconds)
  have normalized : (TimeSpec.mk (Wire.signed 64 (Wire.unsigned 64 t.seconds))
      (Wire.signed 32 (Wire.unsigned 32 t.nanoseconds))) = t := by
    rw [Wire.signed_unsigned64 _ slo shi, Wire.signed_unsigned32 _ nlo nhi]
  exact (congrArg (fun fs => fs.bind decTime) parsed).trans
    ((Option.bind_some _ decTime).trans (decoded.trans (congrArg some normalized)))

private def timeAt (tag : Nat) (fs : List Wire.Field) : Option TimeSpec := do
  decTime (← Wire.getMessage tag fs)

private def encInfo (i : InfoMessage) : List UInt8 :=
  Wire.text 1 i.key ++ match i.value with
  | .number n => Wire.number 2 (Wire.unsigned 64 n)
  | .string s => Wire.text 3 s
  | .strings ss => Wire.bytes 4 ((ss.map (Wire.text 1)).flatten)
  | .numbers ns => Wire.bytes 5 (Wire.bytes 1 ((ns.map (fun n =>
      Wire.encNat (Wire.unsigned 64 n))).flatten))

/-- Packed numbers share the indexed, ten-byte-bounded varint reader and use a
reverse accumulator rather than one stack frame per number. -/
private def packedNumbersAux (bs : ByteArray) : Nat → Nat → List Int → Option (List Int)
  | 0, _, _ => none
  | fuel + 1, pos, acc =>
    if pos = bs.size then some acc.reverse else do
      let (n, next) ← Wire.varintAt bs pos
      if pos < next ∧ next ≤ bs.size then
        packedNumbersAux bs fuel next (Wire.signed 64 n :: acc)
      else none

private def packedNumbers (input : List UInt8) : Option (List Int) :=
  let bs : ByteArray := ⟨input.toArray⟩
  packedNumbersAux bs (bs.size + 1) 0 []

private def decNumbers (fs : List Wire.Field) : Option (List Int) := do
  let chunks ← (Wire.values 1 fs).mapM fun v => match v with
    | .number n => pure [Wire.signed 64 n]
    | .bytes bs => packedNumbers bs
    | _ => none
  pure chunks.flatten

private def decInfoValue (f : Wire.Field) : Option InfoValue := do
  match f with
  | (2, v) => pure (.number (Wire.signed 64 (← Wire.asNumber v)))
  | (3, v) => pure (.string (← Wire.asString v))
  | (4, v) =>
    let fs ← Wire.fields (← Wire.asBytes v)
    pure (.strings (← (Wire.values 1 fs).mapM Wire.asString))
  | (5, v) =>
    let fs ← Wire.fields (← Wire.asBytes v)
    pure (.numbers (← decNumbers fs))
  | _ => none

private def decInfo (fs : List Wire.Field) : Option InfoMessage := do
  let key ← Wire.getString 1 fs
  let value ← Wire.decodeOneof (fun n => decide (2 ≤ n ∧ n ≤ 5))
    (fun n => decide (n = 4 ∨ n = 5)) decInfoValue fs
  pure ⟨key, value⟩

private def infoAt (tag : Nat) (fs : List Wire.Field) : Option (List InfoMessage) :=
  (Wire.values tag fs).mapM fun v => do decInfo (← Wire.fields (← Wire.asBytes v))

private def encInfos (tag : Nat) (info : List InfoMessage) : List UInt8 :=
  (info.map fun i => Wire.bytes tag (encInfo i)).flatten

private def encClient : ClientMessage → List UInt8
  | .hello s => Wire.bytes 13 (Wire.text 1 s)
  | .accept t info expect => Wire.bytes 1
      (Wire.bytes 1 (encTime t) ++ encInfos 2 info ++ Wire.number 3 (if expect then 1 else 0))
  | .reject t reason info => Wire.bytes 2
      (Wire.bytes 1 (encTime t) ++ Wire.text 2 reason ++ encInfos 3 info)
  | .exit t value core signal error => Wire.bytes 3
      (Wire.bytes 1 (encTime t) ++ Wire.number 2 (Wire.unsigned 32 value) ++
       Wire.number 3 (if core then 1 else 0) ++ Wire.text 4 signal ++ Wire.text 5 error)
  | .restart id t => Wire.bytes 4 (Wire.text 1 id ++ Wire.bytes 2 (encTime t))
  | .alert t reason info => Wire.bytes 5
      (Wire.bytes 1 (encTime t) ++ Wire.text 2 reason ++ encInfos 3 info)
  | .io stream t data =>
      if stream < 5 then
        let tag := if stream < 3 then stream + 8 else stream + 3
        Wire.bytes tag (Wire.bytes 1 (encTime t) ++ Wire.bytes 2 data.data.toList)
      else []
  | .winsize t rows cols =>
      if rows < 2 ^ 31 ∧ cols < 2 ^ 31 then Wire.bytes 11
        (Wire.bytes 1 (encTime t) ++ Wire.number 2 rows ++ Wire.number 3 cols)
      else []
  | .suspend t signal => Wire.bytes 12 (Wire.bytes 1 (encTime t) ++ Wire.text 2 signal)

private def decClientField (f : Wire.Field) : Option ClientMessage := do
  let fs ← Wire.fields (← Wire.asBytes f.2)
  match f.1 with
  | 1 => pure (.accept (← timeAt 1 fs) (← infoAt 2 fs) ((← Wire.getNumber 3 fs) != 0))
  | 2 => pure (.reject (← timeAt 1 fs) (← Wire.getString 2 fs) (← infoAt 3 fs))
  | 3 => pure (.exit (← timeAt 1 fs) (Wire.signed 32 (← Wire.getNumber 2 fs))
      ((← Wire.getNumber 3 fs) != 0) (← Wire.getString 4 fs) (← Wire.getString 5 fs))
  | 4 => pure (.restart (← Wire.getString 1 fs) (← timeAt 2 fs))
  | 5 => pure (.alert (← timeAt 1 fs) (← Wire.getString 2 fs) (← infoAt 3 fs))
  | 6 | 7 | 8 | 9 | 10 =>
      let stream := if f.1 < 8 then f.1 - 3 else f.1 - 8
      pure (.io stream (← timeAt 1 fs) (← Wire.getData 2 fs))
  | 11 =>
      let rows := Wire.signed 32 (← Wire.getNumber 2 fs)
      let cols := Wire.signed 32 (← Wire.getNumber 3 fs)
      if rows < 0 ∨ cols < 0 then none
      else pure (.winsize (← timeAt 1 fs) rows.toNat cols.toNat)
  | 12 => pure (.suspend (← timeAt 1 fs) (← Wire.getString 2 fs))
  | 13 => pure (.hello (← Wire.getString 1 fs))
  | _ => none

private def encIoHeader (stream : Nat) (delay : TimeSpec) (size : Nat) : List UInt8 :=
  let tag := if stream < 3 then stream + 8 else stream + 3
  let time := Wire.bytes 1 (encTime delay)
  let dataHeader := Wire.encNat 18 ++ Wire.encNat size
  Wire.encNat (tag * 8 + 2) ++ Wire.encNat (time.length + dataHeader.length + size) ++
    time ++ dataHeader

/-- Encode one unframed client protobuf body. I/O payloads are appended directly
to their small header, without allocating a linked list for each payload byte. -/
def encodeClient (m : ClientMessage) : ByteArray :=
  match m with
  | .io stream delay data =>
    if stream < 5 then (⟨(encIoHeader stream delay data.size).toArray⟩ : ByteArray) ++ data
    else ByteArray.empty
  | _ => ⟨(encClient m).toArray⟩

/-- The allocation-efficient I/O encoder is byte-for-byte identical to the
protobuf field encoder for arbitrary streams, timestamps and binary payloads. -/
theorem encodeClient_io_eq (stream : Nat) (delay : TimeSpec) (data : ByteArray) :
    encodeClient (.io stream delay data) = ⟨(encClient (.io stream delay data)).toArray⟩ := by
  apply ByteArray.ext
  by_cases valid : stream < 5
  · simp [encodeClient, encClient, valid, encIoHeader, Wire.bytes, List.append_assoc,
      List.length_append, Nat.add_assoc]
  · simp [encodeClient, encClient, valid]

/-- Unknown fields are skipped. No recognized oneof case is a protocol failure. -/
def decodeClient (body : ByteArray) : Option ClientMessage := do
  let fs ← Wire.fieldsArray body
  Wire.decodeOneof (fun n => decide (1 ≤ n ∧ n ≤ 13)) (fun _ => true) decClientField fs

private def encHello (h : ServerHello) : List UInt8 :=
  Wire.text 1 h.serverId ++ Wire.text 2 h.redirect ++
  (h.servers.map (Wire.text 3)).flatten ++ Wire.number 4 (if h.subcommands then 1 else 0)

private def decHello (fs : List Wire.Field) : Option ServerHello := do
  pure ⟨← Wire.getString 1 fs, ← Wire.getString 2 fs,
    ← (Wire.values 3 fs).mapM Wire.asString, (← Wire.getNumber 4 fs) != 0⟩

private def encServer : ServerMessage → List UInt8
  | .hello h => Wire.bytes 1 (encHello h)
  | .commit t => Wire.bytes 2 (encTime t)
  | .logId s => Wire.text 3 s
  | .error s => Wire.text 4 s
  | .abort s => Wire.text 5 s

private def decServerField (f : Wire.Field) : Option ServerMessage := do
  match f with
  | (1, v) => pure (.hello (← decHello (← Wire.fields (← Wire.asBytes v))))
  | (2, v) => pure (.commit (← decTime (← Wire.fields (← Wire.asBytes v))))
  | (3, v) => pure (.logId (← Wire.asString v))
  | (4, v) => pure (.error (← Wire.asString v))
  | (5, v) => pure (.abort (← Wire.asString v))
  | _ => none

/-- Encode one unframed server protobuf body. -/
def encodeServer (m : ServerMessage) : ByteArray := ⟨(encServer m).toArray⟩

def decodeServer (body : ByteArray) : Option ServerMessage := do
  let fs ← Wire.fieldsArray body
  Wire.decodeOneof (fun n => decide (1 ≤ n ∧ n ≤ 5))
    (fun n => decide (n = 1 ∨ n = 2)) decServerField fs

private theorem serverText_roundtrip (tag : Nat) (ctor : String → ServerMessage)
    (s : String) (bound : s.toUTF8.size < 2 ^ 64)
    (kind : tag = 3 ∧ ctor = .logId ∨ tag = 4 ∧ ctor = .error ∨
      tag = 5 ∧ ctor = .abort) :
    decodeServer (encodeServer (ctor s)) = some (ctor s) := by
  have bounds : 0 < tag ∧ tag < 16 := by
    rcases kind with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> decide
  have parsed := Wire.fields_bytes_roundtrip tag s.toUTF8.data.toList
    bounds.1 bounds.2 (by simpa using bound)
  have utf8 : Wire.asString (.bytes s.toByteArray.data.toList) = some s :=
    Wire.asString_utf8 s
  rcases kind with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    simp only [encodeServer, encServer, Wire.text, decodeServer, Wire.fieldsArray_toArray] <;>
    rw [parsed] <;> simp [Wire.decodeOneof, Wire.oneof, decServerField, utf8]

/-- Arbitrary bounded log IDs survive the complete server message codec. -/
theorem logId_roundtrip (s : String) (bound : s.toUTF8.size < 2 ^ 64) :
    decodeServer (encodeServer (.logId s)) = some (.logId s) :=
  serverText_roundtrip 3 .logId s bound (by simp)

theorem error_roundtrip (s : String) (bound : s.toUTF8.size < 2 ^ 64) :
    decodeServer (encodeServer (.error s)) = some (.error s) :=
  serverText_roundtrip 4 .error s bound (by simp)

theorem abort_roundtrip (s : String) (bound : s.toUTF8.size < 2 ^ 64) :
    decodeServer (encodeServer (.abort s)) = some (.abort s) :=
  serverText_roundtrip 5 .abort s bound (by simp)

/-- Arbitrary bounded client descriptions survive both protobuf envelopes. -/
theorem clientHello_roundtrip (s : String) (bound : s.toUTF8.size + 11 < 2 ^ 64) :
    decodeClient (encodeClient (.hello s)) = some (.hello s) := by
  have stringBound : s.toUTF8.size < 2 ^ 64 := by omega
  have width := Wire.encNat_length_uint64 s.toUTF8.size stringBound
  simp only [String.toUTF8_eq_toByteArray, String.size_toByteArray] at width bound
  have bodyBound : (Wire.text 1 s).length < 2 ^ 64 := by
    simp [Wire.text, Wire.bytes, show (Wire.encNat 10).length = 1 by decide +kernel]
    omega
  have innerParsed := Wire.fields_bytes_roundtrip 1 s.toUTF8.data.toList (by decide)
    (by decide) (by simpa using stringBound)
  simp only [String.toUTF8_eq_toByteArray] at innerParsed
  have outerParsed := Wire.fields_bytes_roundtrip 13 (Wire.text 1 s) (by decide)
    (by decide) bodyBound
  have utf8 : Wire.asString (.bytes s.toByteArray.data.toList) = some s :=
    Wire.asString_utf8 s
  have decoded : decClientField (13, .bytes (Wire.text 1 s)) = some (.hello s) := by
    simp [decClientField, Wire.asBytes, Wire.text, innerParsed, Wire.getString,
      Wire.values, utf8]
  simp only [encodeClient, encClient, decodeClient, Wire.fieldsArray_toArray]
  rw [outerParsed]
  simp [Wire.decodeOneof, Wire.oneof, decoded]

private theorem decServerField_commit (bs : List UInt8) :
    decServerField (2, .bytes bs) =
      ((Wire.fields bs).bind decTime).bind (fun t => some (.commit t)) := by
  simp [decServerField, Wire.asBytes, Option.bind_assoc]

/-- Every representable signed TimeSpec survives the complete commit codec. -/
theorem commit_roundtrip (t : TimeSpec)
    (slo : -(2 ^ 63) ≤ t.seconds) (shi : t.seconds < 2 ^ 63)
    (nlo : -(2 ^ 31) ≤ t.nanoseconds) (nhi : t.nanoseconds < 2 ^ 31) :
    decodeServer (encodeServer (.commit t)) = some (.commit t) := by
  have sw := Wire.encNat_length_uint64 _ (Wire.unsigned_bound 64 t.seconds)
  have nw := Wire.encNat_length_uint64 _ (Wire.unsigned_bound 32 t.nanoseconds)
  have bodyBound : (encTime t).length < 2 ^ 64 := by
    simp [encTime, Wire.number, show (Wire.encNat 8).length = 1 by decide +kernel,
      show (Wire.encNat 16).length = 1 by decide +kernel]
    omega
  have parsed := Wire.fields_bytes_roundtrip 2 (encTime t) (by decide)
    (by decide) bodyBound
  have decoded : decServerField (2, .bytes (encTime t)) = some (.commit t) := by
    rw [decServerField_commit, time_roundtrip t slo shi nlo nhi]
    rfl
  simp only [encodeServer, encServer, decodeServer, Wire.fieldsArray_toArray]
  rw [parsed]
  simp [Wire.decodeOneof, Wire.oneof, decoded]

/-- Zero-time acceptance, for either value of the I/O negotiation flag. -/
theorem accept_zero_roundtrip (expect : Bool) :
    decodeClient (encodeClient (.accept ⟨0, 0⟩ [] expect)) =
      some (.accept ⟨0, 0⟩ [] expect) := by
  cases expect <;> decide +kernel

/-- Zero-time exit, for either core-dump flag. -/
theorem exit_zero_roundtrip (core : Bool) :
    decodeClient (encodeClient (.exit ⟨0, 0⟩ 0 core "" "")) =
      some (.exit ⟨0, 0⟩ 0 core "" "") := by
  cases core <;> decide +kernel

/-- Every supported I/O stream preserves arbitrary byte values in this binary
boundary vector; stream routing is independent of the transport framing. -/
theorem io_stream_roundtrip (stream : Fin 5) :
    decodeClient (encodeClient (.io stream.val ⟨0, 0⟩ ⟨#[0, 128, 255]⟩)) =
      some (.io stream.val ⟨0, 0⟩ ⟨#[0, 128, 255]⟩) := by
  rcases stream with ⟨stream, bound⟩
  have hcases : stream = 0 ∨ stream = 1 ∨ stream = 2 ∨ stream = 3 ∨ stream = 4 := by omega
  rcases hcases with h | h | h | h | h <;> subst stream <;> dsimp only <;> decide +kernel

/-- Both server subcommand capability values survive the hello handshake. -/
theorem hello_capability_roundtrip (capability : Bool) :
    decodeServer (encodeServer (.hello ⟨"", "", [], capability⟩)) =
      some (.hello ⟨"", "", [], capability⟩) := by
  cases capability <;> decide +kernel

end LeanSudo.LogSrv
