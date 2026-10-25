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
UTF-8, field numbers, lengths, varint overflow, wire types and balanced groups.
Unknown fields are skipped, including deprecated protobuf groups. Scalar fields
have proto3 defaults; repeated numeric values accept packed and unpacked forms.

General roundtrip proofs cover bounded varints, signed scalar normalization,
arbitrary UTF-8 and binary envelopes, TimeSpec, ClientHello, and the server
commit/log-id/error/abort families. Additional finite-family proofs cover I/O
stream routing and capability flags. `Tests.LogSrv` covers every constructor,
malformed inputs, unknown fields, packed lists and a 64 KiB I/O buffer. There is
no claimed universal roundtrip theorem for all ClientMessage/ServerMessage values.
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

/-- Bounded parser rejects overflow and unterminated ten-byte varints. -/
def varint (bs : List UInt8) : Option (Nat × List UInt8) := do
  let (n, rest) ← decNat (bs.take 10)
  if n < 2 ^ 64 then pure (n, rest ++ bs.drop 10) else none

/-- The actual, overflow-checking varint parser preserves arbitrary trailing
bytes for every uint64 whose canonical representation fits the ten-byte limit. -/
theorem varint_encNat (n : Nat) (rest : List UInt8)
    (bound : n < 2 ^ 64) (width : (encNat n).length ≤ 10) :
    varint (encNat n ++ rest) = some (n, rest) := by
  simp [varint, List.take_append, List.take_of_length_le width, decNat_encNat,
    bound, List.drop_append, List.drop_eq_nil_of_le width]

/-- Every bounded uint64 roundtrips through the bounded wire parser. -/
theorem varint_uint64 (n : Nat) (rest : List UInt8) (bound : n < 2 ^ 64) :
    varint (encNat n ++ rest) = some (n, rest) :=
  varint_encNat n rest bound (encNat_length_uint64 n bound)

@[simp] theorem varint_uint64_nil (n : Nat) (bound : n < 2 ^ 64) :
    varint (encNat n) = some (n, []) := by
  simpa using varint_uint64 n [] bound

@[simp] theorem varint_byte (b : UInt8) (rest : List UInt8) (small : b.toNat < 128) :
    varint (b :: rest) = some (b.toNat, rest) := by
  simpa [encNat, small] using varint_uint64 b.toNat rest (by omega)

/-- Read a length-delimited payload, leaving subsequent fields untouched. -/
def blob (bs : List UInt8) : Option (List UInt8 × List UInt8) := do
  let (size, rest) ← varint bs
  if size ≤ rest.length then pure (rest.take size, rest.drop size) else none

/-- Arbitrary binary payloads roundtrip through the actual length parser.
The premises express protobuf's uint64 length/ten-byte varint bounds, not a
decoder-success hypothesis. -/
theorem blob_roundtrip (payload rest : List UInt8)
    (bound : payload.length < 2 ^ 64) (width : (encNat payload.length).length ≤ 10) :
    blob (encNat payload.length ++ payload ++ rest) = some (payload, rest) := by
  simp [blob, List.append_assoc, varint_encNat payload.length (payload ++ rest) bound width]

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

/-- Parse a message or a matched group. Fuel bounds nesting and field count by
input size; it does not impose an arbitrary limit on valid message sizes. -/
def fieldsAux : Nat → Nat → List UInt8 → Option (List Field × List UInt8)
  | 0, _, _ => none
  | _ + 1, ending, [] => if ending = 0 then some ([], []) else none
  | fuel + 1, ending, bs => do
    let (key, rest) ← varint bs
    let number := key / 8
    let kind := key % 8
    if number = 0 ∨ number ≥ 2 ^ 29 then none else do
      if kind = 4 then
        if ending = number then pure ([], rest) else none
      else do
        let (value, rest) ←
          if kind = 0 then do
            let (n, rest) ← varint rest
            pure (Value.number n, rest)
          else if kind = 1 then
            if rest.length ≥ 8 then pure (Value.skipped, rest.drop 8) else none
          else if kind = 2 then do
            let (payload, rest) ← blob rest
            pure (Value.bytes payload, rest)
          else if kind = 3 then do
            let (_, rest) ← fieldsAux fuel number rest
            pure (Value.skipped, rest)
          else if kind = 5 then
            if rest.length ≥ 4 then pure (Value.skipped, rest.drop 4) else none
          else none
        let (following, rest) ← fieldsAux fuel ending rest
        pure ((number, value) :: following, rest)

def fields (bs : List UInt8) : Option (List Field) := do
  let (fs, rest) ← fieldsAux (bs.length + 1) 0 bs
  if rest.isEmpty then pure fs else none

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
case. Unknown fields do not reset a oneof. Strings and numeric cases replace. -/
def oneof (known merge : Nat → Bool) (fs : List Field) : Option Field :=
  fs.foldl (fun selected f =>
    if !known f.1 then selected
    else match selected, f.2 with
      | some (tag, .bytes previous), .bytes next =>
        if tag = f.1 ∧ merge tag then some (tag, .bytes (previous ++ next)) else some f
      | _, _ => some f) none

private theorem fieldsAux_bytes_small (fuel tag : Nat) (payload : List UInt8)
    (positive : 0 < tag) (small : tag < 16) (bound : payload.length < 2 ^ 64) :
    fieldsAux (fuel + 2) 0 (UInt8.ofNat (tag * 8 + 2) :: encNat payload.length ++ payload) =
      some ([(tag, .bytes payload)], []) := by
  have digit : (UInt8.ofNat (tag * 8 + 2)).toNat = tag * 8 + 2 := by
    simp
    omega
  have keySmall : tag * 8 + 2 < 128 := by omega
  have payloadParsed : blob (encNat payload.length ++ payload) = some (payload, []) := by
    simpa using blob_roundtrip payload [] bound (encNat_length_uint64 _ bound)
  have keyParsed := varint_byte (UInt8.ofNat (tag * 8 + 2))
    (encNat payload.length ++ payload) (by rw [digit]; exact keySmall)
  rw [fieldsAux]
  simp only [List.cons_append]
  rw [keyParsed]
  simp only [digit]
  simp [payloadParsed, fieldsAux]
  all_goals first | omega | simp [List.cons_append]

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
  simp only [fields]
  rw [size, fieldsAux_bytes_small _ tag payload positive small bound]
  rfl

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

private theorem fieldsAux_time (fuel a b : Nat) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    Wire.fieldsAux (fuel + 3) 0 (8 :: Wire.encNat a ++ 16 :: Wire.encNat b) =
      some ([(1, .number a), (2, .number b)], []) := by
  simp [Wire.fieldsAux, Wire.varint_uint64 a (16 :: Wire.encNat b) ha, hb]

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
  have size : (8 :: Wire.encNat a ++ 16 :: Wire.encNat b).length + 1 =
      ((Wire.encNat a).length + (Wire.encNat b).length) + 3 := by
    simp only [List.length_cons, List.length_append]
    omega
  simp only [Wire.fields]
  rw [size, fieldsAux_time _ a b ha hb]
  rfl

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

private def packedNumbers : Nat → List UInt8 → Option (List Int)
  | 0, _ => none
  | _ + 1, [] => some []
  | fuel + 1, bs => do
    let (n, rest) ← Wire.varint bs
    let ns ← packedNumbers fuel rest
    pure (Wire.signed 64 n :: ns)

private def decNumbers (fs : List Wire.Field) : Option (List Int) := do
  let chunks ← (Wire.values 1 fs).mapM fun v => match v with
    | .number n => pure [Wire.signed 64 n]
    | .bytes bs => packedNumbers (bs.length + 1) bs
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
  let known := fun n => decide (2 ≤ n ∧ n ≤ 5)
  for f in fs do
    if known f.1 then let _ ← decInfoValue f; pure ()
  let value ← decInfoValue (← Wire.oneof known (fun n => decide (n = 4 ∨ n = 5)) fs)
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
  let fs ← Wire.fields body.data.toList
  let known := fun n => decide (1 ≤ n ∧ n ≤ 13)
  for f in fs do
    if known f.1 then let _ ← decClientField f; pure ()
  decClientField (← Wire.oneof known (fun _ => true) fs)

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
  let fs ← Wire.fields body.data.toList
  let known := fun n => decide (1 ≤ n ∧ n ≤ 5)
  for f in fs do
    if known f.1 then let _ ← decServerField f; pure ()
  decServerField (← Wire.oneof known (fun n => decide (n = 1 ∨ n = 2)) fs)

/-- Arbitrary bounded log IDs survive the complete server message codec. -/
theorem logId_roundtrip (s : String) (bound : s.toUTF8.size < 2 ^ 64) :
    decodeServer (encodeServer (.logId s)) = some (.logId s) := by
  have parsed := Wire.fields_bytes_roundtrip 3 s.toUTF8.data.toList (by decide)
    (by decide) (by simpa using bound)
  have utf8 : Wire.asString (.bytes s.toByteArray.data.toList) = some s :=
    Wire.asString_utf8 s
  simp only [encodeServer, encServer, Wire.text, decodeServer]
  rw [parsed]
  simp [Wire.oneof, decServerField, utf8]

theorem error_roundtrip (s : String) (bound : s.toUTF8.size < 2 ^ 64) :
    decodeServer (encodeServer (.error s)) = some (.error s) := by
  have parsed := Wire.fields_bytes_roundtrip 4 s.toUTF8.data.toList (by decide)
    (by decide) (by simpa using bound)
  have utf8 : Wire.asString (.bytes s.toByteArray.data.toList) = some s :=
    Wire.asString_utf8 s
  simp only [encodeServer, encServer, Wire.text, decodeServer]
  rw [parsed]
  simp [Wire.oneof, decServerField, utf8]

theorem abort_roundtrip (s : String) (bound : s.toUTF8.size < 2 ^ 64) :
    decodeServer (encodeServer (.abort s)) = some (.abort s) := by
  have parsed := Wire.fields_bytes_roundtrip 5 s.toUTF8.data.toList (by decide)
    (by decide) (by simpa using bound)
  have utf8 : Wire.asString (.bytes s.toByteArray.data.toList) = some s :=
    Wire.asString_utf8 s
  simp only [encodeServer, encServer, Wire.text, decodeServer]
  rw [parsed]
  simp [Wire.oneof, decServerField, utf8]

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
  simp only [encodeClient, encClient, decodeClient]
  rw [outerParsed]
  simp [Wire.oneof, decoded]

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
  simp only [encodeServer, encServer, decodeServer]
  rw [parsed]
  simp [Wire.oneof, decoded]

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
