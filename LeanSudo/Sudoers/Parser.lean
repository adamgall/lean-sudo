import LeanSudo.Sudoers.Ast

namespace LeanSudo.Sudoers

structure ParseError where
  file : String
  line : Nat
  col : Nat
  msg : String
  deriving Repr, BEq, Inhabited

def ParseError.toString (e : ParseError) : String :=
  s!"{e.file}:{e.line}:{e.col}: syntax error" ++ (if e.msg.isEmpty then "" else s!": {e.msg}")

instance : ToString ParseError := ⟨ParseError.toString⟩

namespace Parser

structure PChar where
  c : Char
  line : Nat
  col : Nat
  deriving Repr, Inhabited

def annotate : List Char → Nat → Nat → List PChar → List PChar
  | [], _, _, acc => acc.reverse
  | c :: cs, l, k, acc =>
    if c == '\n' then annotate cs (l + 1) 1 (⟨c, l, k⟩ :: acc)
    else annotate cs l (k + 1) (⟨c, l, k⟩ :: acc)

def endPos : List Char → Nat → Nat → Nat × Nat
  | [], l, k => (l, k)
  | c :: cs, l, k => if c == '\n' then endPos cs (l + 1) 1 else endPos cs l (k + 1)

structure Ctx where
  file : String
  eofLine : Nat
  eofCol : Nat
  fuel : Nat

structure ParseState where
  input : List PChar
  warnings : List String := []

abbrev P := ReaderT Ctx (StateT ParseState (Except ParseError))

def get : P (List PChar) := do return (← getThe ParseState).input

def set (input : List PChar) : P Unit :=
  modifyThe ParseState fun s => { s with input }

def modify (f : List PChar → List PChar) : P Unit :=
  modifyThe ParseState fun s => { s with input := f s.input }

def warnAt (pos : Nat × Nat) (message : String) : P Unit := do
  let warning := s!"{(← read).file}:{pos.1}:{pos.2}: {message}"
  modifyThe ParseState fun s => { s with warnings := warning :: s.warnings }

def isBlank (c : Char) : Bool := c == ' ' || c == '\t' || c == '\r'

def isWordChar (c : Char) : Bool :=
  !(isBlank c || c == '\n' || c == '#' || c == '>' || c == '!' || c == '=' || c == ':' ||
    c == ',' || c == '(' || c == ')' || c == '"' || c == '\\')

def isAliasName (s : String) : Bool :=
  match s.toList with
  | c :: cs => c.isUpper && cs.all (fun d => d.isUpper || d.isDigit || d == '_')
  | [] => false

def isTagChar (c : Char) : Bool := c.isUpper || c == '_'

def isCont : List PChar → Bool
  | [] => false
  | c :: cs => if c.c == '\n' then true else if isBlank c.c then isCont cs else false

def skipWsAux : Bool → List PChar → List PChar
  | _, [] => []
  | false, c :: cs =>
    if isBlank c.c then skipWsAux false cs
    else if c.c == '\\' && isCont cs then skipWsAux true cs
    else c :: cs
  | true, c :: cs => if c.c == '\n' then skipWsAux false cs else skipWsAux true cs

def stripPrefix : List PChar → List Char → Option (List PChar)
  | inp, [] => some inp
  | c :: cs, d :: ds => if c.c == d then stripPrefix cs ds else none
  | [], _ :: _ => none

def kwAux : List PChar → List Char → Option (String × Char × List PChar)
  | [], _ => none
  | c :: cs, acc =>
    if isTagChar c.c then kwAux cs (c.c :: acc)
    else
      if acc.isEmpty then none
      else
        match skipWsAux false (c :: cs) with
        | d :: ds => some (String.ofList acc.reverse, d.c, ds)
        | [] => none

def curPos : P (Nat × Nat) := do
  match (← get) with
  | c :: _ => pure (c.line, c.col)
  | [] => let ctx ← read; pure (ctx.eofLine, ctx.eofCol)

def errAt (pos : Nat × Nat) (msg : String) : P α := do
  throw { file := (← read).file, line := pos.1, col := pos.2, msg }

def err (msg : String) : P α := do
  errAt (← curPos) msg

def peek : P (Option Char) := do return (← get).head?.map (·.c)

def peek2 : P (Option Char) := do
  match (← get) with
  | _ :: d :: _ => return some d.c
  | _ => return none

def advance : P Unit := modify List.tail

def ws : P Unit := modify (skipWsAux false)

def fuel : P Nat := do return (← read).fuel

def describe : Option Char → String
  | none => "end of file"
  | some '\n' => "end of line"
  | some c => s!"'{c}'"

def expect (c : Char) : P Unit := do
  let p ← peek
  if p == some c then advance else err s!"expected '{c}', found {describe p}"

def hexDigit (c : Char) : Option Nat :=
  if c.isDigit then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

def charBytes (c : Char) : List UInt8 := (String.singleton c).toUTF8.data.toList

def decodedWord (reversed : List UInt8) : P String := do
  let bytes := reversed.reverse.takeWhile (· != 0)
  match String.fromUTF8? (ByteArray.mk bytes.toArray) with
  | some s => return s
  | none => err "non-UTF-8 escaped string"

def wordEscape : P (List UInt8) := do
  match (← get) with
  | x :: a :: b :: rest =>
    if x.c == 'x' then
      if let (some hi, some lo) := (hexDigit a.c, hexDigit b.c) then
        set rest
        return [(hi * 16 + lo).toUInt8]
    advance
    return charBytes x.c
  | x :: _ => advance; return charBytes x.c
  | [] => err "unterminated escape"

def escapedRun (breakEscape : Char → Bool) (stop : Bool → Char → Bool) :
    P (List UInt8 × Bool) := do
  let mut acc : List UInt8 := []
  let mut esc := false
  for _ in [0:(← fuel)] do
    match (← get) with
    | c :: cs =>
      if c.c == '\\' then
        match cs with
        | d :: _ =>
          if breakEscape d.c || isCont cs then break
          set cs
          esc := true
          acc := (← wordEscape).reverse ++ acc
        | [] => break
      else if !stop acc.isEmpty c.c then
        set cs
        acc := (charBytes c.c).reverse ++ acc
      else break
    | [] => break
  return (acc, esc)

def readWord : P (String × Bool) := do
  let (acc, esc) ← escapedRun (· == '\t') (fun _ c => !isWordChar c)
  return (← decodedWord acc, esc)

def readQuoted : P String := do
  expect '"'
  let mut acc : List UInt8 := []
  for _ in [0:(← fuel)] do
    match (← get) with
    | [] => err "unterminated quoted string"
    | c :: cs =>
      if c.c == '"' then
        set cs
        if acc.isEmpty then err "empty string"
        return (← decodedWord acc)
      else if c.c == '\n' then err "unterminated quoted string"
      else if c.c == '\\' then
        if isCont cs then set (skipWsAux false (c :: cs))
        else
          match cs with
          | d :: ds =>
            if d.c == '"' then
              set ds
              acc := '"'.toNat.toUInt8 :: acc
            else
              set cs
              acc := '\\'.toNat.toUInt8 :: acc
          | [] => err "unterminated quoted string"
      else
        set cs
        acc := (charBytes c.c).reverse ++ acc
  err "unterminated quoted string"

def foldChars (p : Char → Bool) (step : α → Char → α) (init : α) : P α := do
  let mut acc := init
  for _ in [0:(← fuel)] do
    match (← peek) with
    | some c =>
      if !p c then break
      advance
      acc := step acc c
    | none => break
  return acc

def takeChars (p : Char → Bool) (input : List PChar) : List Char :=
  (input.takeWhile (fun c => p c.c)).map (·.c)

def readNat : P Nat := do
  if (← fuel) == 0 || !(← peek).any Char.isDigit then err "expected a numeric id"
  let n ← foldChars Char.isDigit (fun n c => n * 10 + (c.toNat - '0'.toNat)) 0
  match (← peek) with
  | some c => if isWordChar c || c == '\\' then err "invalid numeric id" else pure n
  | none => pure n

def negCount : P Nat := do
  ws
  let n ← foldChars (· == '!') (fun n _ => n + 1) 0
  ws
  return n

def member (atom : P α) : P (Member α) := do
  let n ← negCount
  let a ← atom
  return ⟨n % 2 == 1, a⟩

def sepBy1 (sep : Char) (item : P α) (tooLong : String) : P (List α) := do
  let mut acc := [← item]
  for _ in [0:(← fuel)] do
    ws
    if (← peek) == some sep then
      advance
      ws
      acc := (← item) :: acc
    else return acc.reverse
  err tooLong

def list1 (item : P α) : P (List α) := sepBy1 ',' item "list too long"

def userAtom : P UserAtom := do
  match (← peek) with
  | some '#' =>
    advance
    return .id (← readNat)
  | some '%' =>
    advance
    match (← peek) with
    | some ':' =>
      advance
      if (← peek) == some '#' then
        advance
        return .nonunixGid (← readNat)
      let (w, _) ← readWord
      if w.isEmpty then err "empty group"
      return .nonunixGroup w
    | some '#' =>
      advance
      return .gid (← readNat)
    | some '"' => err "empty group"
    | p =>
      let (w, _) ← readWord
      if w.isEmpty then err s!"expected a group name, found {describe p}"
      return .group w
  | some '+' =>
    advance
    let (w, _) ← readWord
    if w.isEmpty then err "empty netgroup"
    return .netgroup w
  | some '"' =>
    let w ← readQuoted
    if w.startsWith "%:#" then
      if let some n := (String.ofList (w.toList.drop 3)).toNat? then return .nonunixGid n
    if w.startsWith "%:" then
      let n := String.ofList (w.toList.drop 2)
      if n.isEmpty then err "empty group"
      return .nonunixGroup n
    if w.startsWith "%#" then
      if let some n := (String.ofList (w.toList.drop 2)).toNat? then return .gid n
    if w.startsWith "%" || w.startsWith "+" then
      let n := String.ofList w.toList.tail
      if n.isEmpty then err "empty group or netgroup"
      return if w.startsWith "%" then .group n else .netgroup n
    if w.startsWith "#" then
      if let some n := (String.ofList w.toList.tail).toNat? then return .id n
    return .name w
  | p =>
    let pos ← curPos
    let (w, esc) ← readWord
    if w.isEmpty then errAt pos s!"expected a user name, found {describe p}"
    if !esc && w == "ALL" then return .all
    if !esc && isAliasName w then return .alias w
    return .name w

def ipv4 (s : String) : Option (List UInt8) := do
  let parts := s.splitOn "."
  if parts.length != 4 then none else do
    parts.mapM fun p => do
      let n ← p.toNat?
      if p.isEmpty || n > 255 then none else some n.toUInt8

def hexWord (s : String) : Option Nat := do
  if s.isEmpty || s.length > 4 then none else
    s.toList.foldlM (fun n c => return n * 16 + (← hexDigit c)) 0

def ipv6Part (s : String) : Option (List Nat) := do
  if s.isEmpty then return []
  let ps := s.splitOn ":"
  let mut out := []
  let mut dotted := false
  for p in ps do
    if dotted then none else pure ()
    if p.contains '.' then
      dotted := true
      let bs ← ipv4 p
      match bs with
      | [a,b,c,d] => out := out ++ [a.toNat * 256 + b.toNat, c.toNat * 256 + d.toNat]
      | _ => none
    else out := out ++ [← hexWord p]
  return out

def ipAddress (s : String) : Option IpAddr := do
  if !s.contains ':' then return .v4 (← ipv4 s)
  let words ← match s.splitOn "::" with
    | [a] => do
      let ws ← ipv6Part a
      if ws.length == 8 then some ws else none
    | [a,b] => do
      let lhs ← ipv6Part a
      let rhs ← ipv6Part b
      if lhs.length + rhs.length ≥ 8 then none
      else some (lhs ++ List.replicate (8 - lhs.length - rhs.length) 0 ++ rhs)
    | _ => none
  return .v6 (words.flatMap fun n => [(n / 256).toUInt8, n.toUInt8])

def network (s : String) : Option HostAtom := do
  let (a, mask) ← match s.splitOn "/" with
    | [a] => some (a, none)
    | [a,m] => some (a, some m)
    | _ => none
  let addr ← ipAddress a
  let width := match addr with | .v4 _ => 4 | .v6 _ => 16
  let mk := match addr with | .v4 _ => IpAddr.v4 | .v6 _ => IpAddr.v6
  let bitsMask (bits : Nat) := mk ((List.range width).map fun i =>
    (256 - 2 ^ (8 - min 8 (bits - i * 8))).toUInt8)
  let m ← match mask with
    | none => some (mk [])
    | some text =>
      match text.toNat? with
      | some n => some (if 0 < n && n ≤ width * 8 then bitsMask n else mk [0])
      | none => do
        let m ← ipAddress text
        match addr, m with
        | .v4 _, .v4 _ | .v6 _, .v6 _ => some m
        | _, _ => none
  return .network addr m

def hostAtom : P HostAtom := do
  if (← peek) == some '"' then
    let w ← readQuoted
    if w.startsWith "+" then
      let n := String.ofList w.toList.tail
      if n.isEmpty then err "empty netgroup"
      return .netgroup n
    if w.startsWith "%" then err "expected a host name"
    return .name w
  if (← peek) == some '+' then
    advance
    let (w, _) ← readWord
    if w.isEmpty then err "empty netgroup"
    return .netgroup w
  let inp ← get
  let candidate := takeChars (fun c =>
    !isBlank c && c != '\n' && c != ',' && c != '=' && c != '#') inp
  if let some net := network (String.ofList candidate) then
    set (inp.drop candidate.length)
    return net
  let pos ← curPos
  let (w, esc) ← readWord
  if w.isEmpty then errAt pos "expected a host name"
  if !esc && w == "ALL" then return .all
  if !esc && isAliasName w then return .alias w
  return .name w

def isCmdTerminator (c : Char) : Bool :=
  isBlank c || c == '\n' || c == '#' || c == ':' || c == ','

def readCmdWord (isPath : Bool) : P String := do
  let mut acc : List Char := []
  for _ in [0:(← fuel)] do
    match (← get) with
    | [] => break
    | c :: cs =>
      if c.c == '\\' then
        if isCont cs then break
        match cs with
        | d :: ds =>
          if d.c == '*' || d.c == '?' || d.c == '[' || d.c == ']' || d.c == '!' || d.c == '^' then
            set ds
            acc := d.c :: '\\' :: acc
          else if d.c == ':' || (d.c == '\\' && !isPath) || d.c == ',' || d.c == '=' || d.c == ' ' ||
              d.c == '\t' || d.c == '#' then
            set ds
            acc := d.c :: acc
          else
            set ds
            acc := d.c :: '\\' :: acc
        | [] => err "invalid escape at end of file"
      else if isCmdTerminator c.c || (isPath && c.c == '=') then break
      else
        set cs
        acc := c.c :: acc
  return String.ofList acc.reverse

def wordTokenLength : List PChar → Nat
  | c :: d :: rest =>
    if c.c == '\\' && d.c != '\t' && d.c != '\n' then 2 + wordTokenLength rest
    else if isWordChar c.c then 1 + wordTokenLength (d :: rest) else 0
  | [c] => if isWordChar c.c then 1 else 0
  | [] => 0

def readPathRegex : P String := do
  expect '^'
  let mut acc := ['^']
  let mut best : Option (List Char × List PChar) := none
  let finish (candidate : Option (List Char × List PChar)) : P String :=
    match candidate with
    | some (chars, rest) => do set rest; return String.ofList chars.reverse
    | none => err "unterminated regular expression"
  for _ in [0:(← fuel)] do
    match (← get) with
    | [] => return (← finish best)
    | c :: cs =>
      if c.c == '\n' || c.c == '\r' || c.c == '#' then return (← finish best)
      if c.c == '\\' then
        if let d :: ds := cs then
          if d.c == '#' || d.c == '$' then
            set ds
            acc := d.c :: '\\' :: acc
            if d.c == '$' then best := some (acc, ds)
            continue
      set cs
      acc := c.c :: acc
      if c.c == '$' then return String.ofList acc.reverse
  finish best

def readRegex : P String := do
  expect '^'
  let mut acc := ['^']
  for _ in [0:(← fuel)] do
    match (← get) with
    | [] => err "unterminated regular expression"
    | c :: cs =>
      if c.c == '\n' || c.c == '\r' || c.c == '#' then err "unterminated regular expression"
      if c.c == '\\' then
        if isCont cs then ws
        else
          match cs with
          | d :: ds =>
            if d.c == '\n' || d.c == '\r' then err "unterminated regular expression"
            set ds
            acc := d.c :: '\\' :: acc
          | [] => err "unterminated regular expression"
      else
        set cs
        acc := c.c :: acc
        if c.c == '$' then return String.ofList acc.reverse
  err "unterminated regular expression"

def cmndArgs : P CmndArgs := do
  ws
  if (← peek) == some '^' then return .regex (← readRegex)
  let mut words : List String := []
  for _ in [0:(← fuel)] do
    ws
    match (← peek) with
    | none => break
    | some c =>
      if c == '\n' || c == ',' || c == ':' || c == '#' then break
      let w ← readCmdWord false
      if w.isEmpty then err s!"unexpected {describe (some c)} in command arguments"
      words := w :: words
  match words.reverse with
  | [] => return .any
  | ["\"\""] => return .none
  | ws' =>
    let s := " ".intercalate ws'
    return .pattern s

def digestPrefixes : List (String × DigestAlgo × Nat) :=
  [("sha224", .sha224, 28), ("sha256", .sha256, 32),
   ("sha384", .sha384, 48), ("sha512", .sha512, 64)]

def decodeHex : List Char → Option (List UInt8)
  | [] => some []
  | a :: b :: rest => do
    let hi ← hexDigit a
    let lo ← hexDigit b
    return (hi * 16 + lo).toUInt8 :: (← decodeHex rest)
  | _ => none

def base64Digit (c : Char) : Option Nat :=
  if 'A' ≤ c && c ≤ 'Z' then some (c.toNat - 'A'.toNat)
  else if 'a' ≤ c && c ≤ 'z' then some (c.toNat - 'a'.toNat + 26)
  else if c.isDigit then some (c.toNat - '0'.toNat + 52)
  else if c == '+' then some 62 else if c == '/' then some 63 else none

def decodeDigest (s : String) (size : Nat) : Option (List UInt8) := do
  if s.length == size * 2 then
    if let some bs := decodeHex s.toList then return bs
  let chars := s.toList.takeWhile (· != '=')
  let padding := s.toList.drop chars.length
  if !padding.all (· == '=') || padding.length > 2 then none else do
    if s.length != (size * 4 + 2) / 3 &&
        !(s.length == 4 * ((size + 2) / 3) && !padding.isEmpty) then none else do
      let mut accum := 0
      let mut bits := 0
      let mut bytes := []
      for c in chars do
        accum := accum * 64 + (← base64Digit c)
        bits := bits + 6
        if bits ≥ 8 then
          bits := bits - 8
          bytes := (accum / 2 ^ bits).toUInt8 :: bytes
          accum := accum % 2 ^ bits
      if bytes.length != size then none else some bytes.reverse

def digestStart (inp : List PChar) : Option (DigestAlgo × Nat × List PChar) :=
  digestPrefixes.findSome? fun (name, algo, size) => do
    let rest ← stripPrefix inp name.toList
    match skipWsAux false rest with
    | c :: cs => if c.c == ':' then some (algo, size, cs) else none
    | [] => none

def readDigests : P (List Digest) := do
  let mut ds := []
  for _ in [0:(← fuel)] do
    let some (algo, size, rest) := digestStart (← get) | return ds.reverse
    set rest
    ws
    let inp ← get
    let chars := takeChars (fun c => (base64Digit c).isSome || c == '=') inp
    set (inp.drop chars.length)
    let spelling := String.ofList chars
    let some bytes := decodeDigest spelling size | err "invalid digest"
    ds := { algo, bytes, spelling } :: ds
    ws
    if (← peek) != some ',' then return ds.reverse
    advance
    ws
    if (digestStart (← get)).isNone then err "expected a digest"
  err "digest list too long"

def plainCmndAtom (allowArgs : Bool) : P CmndAtom := do
  match (← peek) with
  | some '/' =>
    let p ← readCmdWord true
    let args ← if allowArgs && !p.endsWith "/" then cmndArgs else pure .any
    if (p.splitOn "/").getLast? == some "sudoedit" then return .sudoedit args
    return .command p args
  | some '^' =>
    let start ← get
    let pos ← curPos
    let re ← readPathRegex
    if wordTokenLength start > re.length then
      errAt pos "expected a fully-qualified path name"
    return .commandRegex re (← if allowArgs then cmndArgs else pure .any)
  | p =>
    let pos ← curPos
    let (w, esc) ← readWord
    if w.isEmpty then errAt pos s!"expected a command, found {describe p}"
    if !esc && w == "ALL" then return .all
    if !esc && isAliasName w then return .alias w
    if w == "sudoedit" then
      return .sudoedit (← if allowArgs then cmndArgs else pure .any)
    if w == "list" then return .list
    errAt pos s!"expected a fully-qualified path name, found \"{w}\""

def cmndMember (allowArgs : Bool) : P (Member CmndAtom) := do
  let ds ← readDigests
  let cmd ← member (plainCmndAtom allowArgs)
  if ds.isEmpty then return cmd
  match cmd.atom with
  | .command .. | .commandRegex .. | .sudoedit .. | .list | .all =>
    return { cmd with atom := .digest ds cmd.atom }
  | _ => err "a digest requires a path name"

def groupAtom : P UserAtom := do
  let a ← userAtom
  match a with
  | .name _ | .id _ | .all | .alias _ => return a
  | _ => err "expected a run-as group name"

def runasSpec : P RunasSpec := do
  expect '('
  ws
  let p ← peek
  let implicitUser := p == some ')' || p == some ':'
  let users ← if implicitUser then pure [⟨false, .myself⟩] else list1 (member userAtom)
  ws
  let mut groups := none
  if (← peek) == some ':' then
    advance
    ws
    if !implicitUser || (← peek) != some ')' then
      groups := some (← list1 (member groupAtom))
      ws
  expect ')'
  return { users := some users, groups }

structure Inherit where
  runas : Option RunasSpec := none
  options : CmndOptions := {}
  tags : Tags := {}

def parseTimeout (s : String) : Option Nat := do
  let mut rest := s.toList
  let mut total := 0
  let mut previous := 0
  for _ in [0:s.length + 1] do
    rest := rest.dropWhile Char.isWhitespace
    let negative := rest.head? == some '-'
    if rest.head? == some '+' || negative then rest := rest.tail
    let digits := rest.takeWhile Char.isDigit
    let n ← (String.ofList digits).toNat?
    if negative && n != 0 then none else pure ()
    rest := rest.drop digits.length
    let scale ← match rest with
      | [] => some 1
      | c :: cs => do
        let (rank, scale) ← match c.toLower with
          | 'd' => some (0, 86400) | 'h' => some (1, 3600)
          | 'm' => some (2, 60) | 's' => some (3, 1)
          | _ => none
        if rank < previous then none else pure ()
        previous := rank
        rest := cs
        some scale
    total := total + n * scale
    if total > 2147483647 then none else pure ()
    if rest.isEmpty then return total
  none

def civilDays (year month day : Nat) : Int :=
  let month : Int := month
  let y : Int := year + (month - 1) / 12
  let m : Int := (month - 1) % 12 + 1
  let y := y - (if m ≤ 2 then 1 else 0)
  let era := y / 400
  let yoe := y - era * 400
  let doy := (153 * (m + (if m > 2 then -3 else 9)) + 2) / 5 + day - 1
  era * 146097 + yoe * 365 + yoe / 4 - yoe / 100 + doy - 719468

def parseGentime (s : String) : Option Nat := do
  let cs := s.toList
  let digits := cs.takeWhile Char.isDigit
  if !([10,12,14] : List Nat).contains digits.length then none else do
    let number (start len : Nat) :=
      (String.ofList (digits.drop start |>.take len)).toNat?.getD 0
    let mut rest := cs.drop digits.length
    let mut extra := 0
    match rest with
    | sep :: d :: tail =>
      if (sep == '.' || sep == ',') && d.isDigit then
        extra := (d.toNat - '0'.toNat) *
          (if digits.length == 10 then 360 else if digits.length == 12 then 6 else 0)
        rest := tail
    | _ => pure ()
    let offset ← match rest with
      | [] | ['Z'] => some (0 : Int)
      | sign :: ds => do
        if (sign != '+' && sign != '-') || !(ds.length == 2 || ds.length == 4) ||
            !ds.all Char.isDigit then none else do
          let h ← (String.ofList (ds.take 2)).toNat?
          let m := (String.ofList (ds.drop 2)).toNat?.getD 0
          some ((if sign == '-' then -1 else 1) * Int.ofNat (h * 3600 + m * 60))
    let seconds := civilDays (number 0 4) (number 4 2) (number 6 2) * 86400 +
      number 8 2 * 3600 + number 10 2 * 60 + number 12 2 + extra - offset
    if seconds == -1 then none else some seconds.toNat

def optionValue : P String := do
  ws
  let w ← if (← peek) == some '"' then readQuoted else Prod.fst <$> readWord
  if w.isEmpty then err "missing option value"
  return w

def directoryValue (name : String) : P String := do
  let w ← optionValue
  if w == "*" || w.startsWith "/" || w.startsWith "~" then return w
  err s!"{name} must begin with '/', '~', or '*'"

def optionNames : List String :=
  ["CWD", "CHROOT", "TIMEOUT", "NOTBEFORE", "NOTAFTER", "ROLE", "TYPE",
   "APPARMOR_PROFILE", "PRIVS", "LIMITPRIVS"]

def cmndSpec (inh : Inherit) : P (CmndSpec × Inherit) := do
  ws
  let mut runas := inh.runas
  let runasExplicit := (← peek) == some '('
  if runasExplicit then
    runas := some (← runasSpec)
  let mut options := inh.options
  let mut roleWritten := false
  let mut privsWritten := false
  let mut optionsExplicit := []
  for _ in [0:(← fuel)] do
    ws
    match kwAux (← get) [] with
    | some (w, '=', rest) =>
      if !optionNames.contains w then break
      set rest
      if w != "TIMEOUT" && w != "NOTBEFORE" && w != "NOTAFTER" then
        optionsExplicit := w :: optionsExplicit
      match w with
      | "CWD" =>
        let v ← directoryValue w
        options := { options with cwd := some (if v == "*" then none else some v) }
      | "CHROOT" =>
        ws
        let start ← curPos
        let quoted := (← peek) == some '"'
        let value ← directoryValue w
        let finish ← curPos
        let pos := if quoted then (finish.1, finish.2 - 1) else start
        warnAt pos "\"CHROOT\" is deprecated"
        options := { options with chroot := some value }
      | "TIMEOUT" =>
        let some n := parseTimeout (← optionValue) | err "invalid timeout"
        options := { options with timeout := some n }
      | "NOTBEFORE" | "NOTAFTER" =>
        let text ← optionValue
        let some n := parseGentime text | err "invalid time specification"
        let isLocal := !text.endsWith "Z" && !text.contains '+' && !text.contains '-'
        if w == "NOTBEFORE" then
          options := { options with notBefore := some n, notBeforeLocal := isLocal }
        else options := { options with notAfter := some n, notAfterLocal := isLocal }
      | "ROLE" | "TYPE" =>
        if !roleWritten then options := { options with role := none, type := none }
        roleWritten := true
        let v ← optionValue
        if w == "ROLE" then options := { options with role := some v }
        else options := { options with type := some v }
      | "PRIVS" | "LIMITPRIVS" =>
        if !privsWritten then options := { options with privs := none, limitprivs := none }
        privsWritten := true
        let v ← optionValue
        if w == "PRIVS" then options := { options with privs := some v }
        else options := { options with limitprivs := some v }
      | "APPARMOR_PROFILE" => options := { options with apparmorProfile := some (← optionValue) }
      | _ => pure ()
    | _ => break
  let mut tags := inh.tags
  for _ in [0:(← fuel)] do
    ws
    match kwAux (← get) [] with
    | some (w, ':', rest) =>
      if w == "PASSWD" then tags := { tags with passwd := some true }
      else if w == "NOPASSWD" then tags := { tags with passwd := some false }
      else if w == "SETENV" then tags := { tags with setenv := some true }
      else if w == "NOSETENV" then tags := { tags with setenv := some false }
      else if w == "NOEXEC" || w == "EXEC" then tags := { tags with noexec := some (w == "NOEXEC") }
      else if w == "INTERCEPT" || w == "NOINTERCEPT" then tags := { tags with intercept := some (w == "INTERCEPT") }
      else if w == "LOG_INPUT" || w == "NOLOG_INPUT" then tags := { tags with logInput := some (w == "LOG_INPUT") }
      else if w == "LOG_OUTPUT" || w == "NOLOG_OUTPUT" then tags := { tags with logOutput := some (w == "LOG_OUTPUT") }
      else if w == "MAIL" || w == "NOMAIL" then tags := { tags with mail := some (w == "MAIL") }
      else if w == "FOLLOW" || w == "NOFOLLOW" then tags := { tags with follow := some (w == "FOLLOW") }
      else break
      set rest
    | _ => break
  let cmnd ← cmndMember true
  return ({ runas, options, tags, cmnd, runasExplicit, optionsExplicit := optionsExplicit.reverse },
    { runas, options, tags })

def cmndSpecList : P (List CmndSpec) := do
  let (s, i) ← cmndSpec {}
  let mut acc := [s]
  let mut inh := i
  for _ in [0:(← fuel)] do
    ws
    if (← peek) == some ',' then
      advance
      let (s, i) ← cmndSpec inh
      acc := s :: acc
      inh := i
    else return acc.reverse
  err "command list too long"

def hostCmnds : P HostCmnds := do
  let hosts ← list1 (member hostAtom)
  ws
  expect '='
  ws
  let cmnds ← cmndSpecList
  return { hosts, cmnds }

private def sourcePosition (stop : Nat × Nat) (extra : Nat) : List PChar → Nat × Nat
  | [] => (stop.1, stop.2 + extra)
  | c :: cs =>
    if c.line > stop.1 || (c.line == stop.1 && c.col >= stop.2) then
      (stop.1, stop.2 + extra)
    else
      let n := c.c.toNat
      let extra := if c.line != stop.1 then extra else
        extra + (if n < 0x80 then 0 else if n < 0x800 then 1 else if n < 0x10000 then 2 else 3)
      sourcePosition stop extra cs

def userSpec : P UserSpec := do
  let before ← get
  let users ← list1 (member userAtom)
  ws
  let entries ← sepBy1 ':' hostCmnds "user specification too long"
  return { users, entries, source := some (sourcePosition (← curPos) 0 before) }

def aliasName : P String := do
  ws
  let pos ← curPos
  let p ← peek
  let (w, esc) ← readWord
  if w.isEmpty then errAt pos s!"expected an alias name, found {describe p}"
  if esc || !isAliasName w then errAt pos s!"invalid alias name \"{w}\""
  if ("ALL" :: optionNames).contains w then
    errAt pos s!"\"{w}\" is a reserved word and cannot be used as an alias name"
  return w

def aliasDefs (item : P α) : P (List (String × List α)) :=
  sepBy1 ':' (do
    let name ← aliasName
    ws
    expect '='
    ws
    return (name, ← list1 item)) "alias definition too long"

def bareValue : P String := do
  let (acc, _) ← escapedRun (fun _ => false) fun empty c =>
    isBlank c || c == '\n' || c == '"' || c == '#' || c == '=' ||
      c == ',' || (empty && c == '!')
  if acc.isEmpty then err "missing value"
  return (← decodedWord acc)

def defaultsValue : P String := do
  ws
  if (← peek) == some '"' then readQuoted else bareValue

def readName : P String := do
  let chars ← foldChars (fun c => ('a' ≤ c && c ≤ 'z') || c == '_') (fun cs c => c :: cs) []
  return String.ofList chars.reverse

def defaultsSetting : P DefaultsSetting := do
  let n ← negCount
  let pos ← curPos
  let p ← peek
  let name ← readName
  if name.isEmpty then errAt pos s!"expected a Defaults setting, found {describe p}"
  ws
  let withValue (mk : String → DefaultsOp) : P DefaultsSetting := do
    if n != 0 then errAt pos s!"negated Defaults setting \"{name}\" cannot take a value"
    ws
    let start ← curPos
    let quoted := (← peek) == some '"'
    let value ← defaultsValue
    let finish ← curPos
    let pos := if quoted then (finish.1, finish.2 - 1) else start
    return { name, op := mk value, source := some ((← read).file, pos.1, pos.2) }
  match (← peek), (← peek2) with
  | some '+', some '=' =>
    advance; advance
    withValue .add
  | some '-', some '=' =>
    advance; advance
    withValue .remove
  | some '=', _ =>
    advance
    withValue .assign
  | _, _ =>
    let next ← curPos
    let pos := if n != 0 then pos else next
    return { name, op := .flag (n % 2 == 0), source := some ((← read).file, pos.1, pos.2) }

def defaultsEntry : P Entry := do
  let original ← get
  let scope ← match (← peek) with
    | some '@' => do advance; ws; pure (DefaultsScope.host (← list1 (member hostAtom)))
    | some ':' => do advance; ws; pure (DefaultsScope.user (← list1 (member userAtom)))
    | some '>' => do advance; ws; pure (DefaultsScope.runas (← list1 (member userAtom)))
    | some '!' => do advance; ws; pure (DefaultsScope.cmnd (← list1 (cmndMember false)))
    | _ => pure DefaultsScope.global
  if scope != .global then
    let consumed := original.take (original.length - (← get).length)
    if !(consumed.getLast?.map (fun c => c.c.isWhitespace)).getD false then
      err "expected whitespace after Defaults binding"
  ws
  return .defaults scope (← list1 defaultsSetting)

def includePath : P String := do
  ws
  if (← peek) == some '"' then return (← readQuoted)
  let (acc, _) ← escapedRun (fun _ => false) (fun _ c => isBlank c || c == '\n')
  if acc.isEmpty then err "missing include path"
  return (← decodedWord acc)

def skipComment : P Unit := do
  for _ in [0:(← fuel)] do
    match (← get) with
    | [] => break
    | c :: cs =>
      set cs
      if c.c == '\n' then break

def endOfEntry : P Unit := do
  ws
  match (← get) with
  | [] => pure ()
  | c :: cs =>
    if c.c == '\n' then set cs
    else if c.c == '#' && !(cs.head?.map (·.c.isDigit)).getD false then skipComment
    else err s!"unexpected {describe (some c.c)}"

def keyword (inp : List PChar) (kw : String) : Option (List PChar) :=
  match stripPrefix inp kw.toList with
  | some (c :: cs) =>
    if isBlank c.c || (c.c == '\\' && isCont cs) then some (c :: cs) else none
  | _ => none

def defaultsKeyword (inp : List PChar) : Option (List PChar) :=
  match stripPrefix inp "Defaults".toList with
  | some [] => some []
  | some (c :: cs) =>
    if isBlank c.c || c.c == '\n' || c.c == '@' || c.c == ':' || c.c == '>' || c.c == '!' ||
        (c.c == '\\' && isCont cs) then some (c :: cs)
    else none
  | none => none

def entry : P (List Entry) := do
  let inp ← get
  let try1 (kw : String) (k : P (List Entry)) : Option (P (List Entry)) :=
    (keyword inp kw).map fun rest => do set rest; k
  let incl (rest : List PChar) (dir : Bool) : P (List Entry) := do
    set rest
    let p ← includePath
    return [if dir then .includeDir p else .include p]
  match keyword inp "#includedir", keyword inp "#include",
      keyword inp "@includedir", keyword inp "@include" with
  | some r, _, _, _ => incl r true
  | _, some r, _, _ => incl r false
  | _, _, some r, _ => incl r true
  | _, _, _, some r => incl r false
  | none, none, none, none =>
  if let some rest := defaultsKeyword inp then
    set rest
    return [← defaultsEntry]
  let aliases : List (Option (P (List Entry))) := [
    try1 "User_Alias" do
      return (← aliasDefs (member userAtom)).map fun (n, ms) => .userAlias n ms,
    try1 "Runas_Alias" do
      return (← aliasDefs (member userAtom)).map fun (n, ms) => .runasAlias n ms,
    try1 "Host_Alias" do
      return (← aliasDefs (member hostAtom)).map fun (n, ms) => .hostAlias n ms,
    ["Cmnd_Alias", "Cmd_Alias"].findSome? fun kw => try1 kw do
      return (← aliasDefs (cmndMember true)).map fun (n, ms) => .cmndAlias n ms]
  match aliases.findSome? id with
  | some k => k
  | none => return [.userSpec (← userSpec)]

def entries : P (List Located) := do
  let file := (← read).file
  let mut acc : List Located := []
  for _ in [0:(← fuel)] do
    ws
    match (← get) with
    | [] => return acc.reverse
    | c :: cs =>
      if c.c == '\n' then
        set cs
        continue
      if c.c == '#' && !(cs.head?.map (·.c.isDigit)).getD false &&
          (c.col != 1 || ((keyword (c :: cs) "#include").isNone &&
            (keyword (c :: cs) "#includedir").isNone)) then
        skipComment
        continue
      let es ← entry
      endOfEntry
      let warnings := (← getThe ParseState).warnings.reverse
      modifyThe ParseState fun s => { s with warnings := [] }
      acc := (es.reverse.map fun e => { file, line := c.line, entry := e, warnings }) ++ acc
  err "input too long"

def cmndAtoms : Entry → List CmndAtom
  | .cmndAlias _ ms => ms.map (·.atom)
  | .defaults (.cmnd cs) _ => cs.map (·.atom)
  | .userSpec s => s.entries.flatMap fun hc => hc.cmnds.map (·.cmnd.atom)
  | _ => []

def CmndAtom.pathOk : CmndAtom → Bool
  | .command p _ => p.toList.head? == some '/'
  | .commandRegex re _ => re.startsWith "^" && re.endsWith "$"
  | .digest ds c => !ds.isEmpty && CmndAtom.pathOk c
  | _ => true

def wellFormed (file : String) (l : Located) : Bool :=
  decide (1 ≤ l.line) && l.file == file && (cmndAtoms l.entry).all CmndAtom.pathOk

def check (file : String) (es : List Located) : Except ParseError (List Located) :=
  match es.find? (fun l => !wellFormed file l) with
  | some l => .error { file, line := l.line, col := 1, msg := "internal error: malformed entry" }
  | none => .ok es

theorem check_ok {file : String} {es es' : List Located} (h : check file es = .ok es') :
    ∀ l ∈ es', wellFormed file l = true := by
  unfold check at h
  split at h
  · cases h
  · rename_i hf
    cases h
    intro l hl
    simpa using List.find?_eq_none.mp hf l hl

def context (file text : String) : Ctx :=
  let cs := text.toList
  let (el, ec) := endPos cs 1 1
  { file, eofLine := el, eofCol := ec, fuel := cs.length + 1 }

end Parser

open Parser in
def parse (file : String) (text : String) : Except ParseError (List Located) :=
  match (entries (context file text)).run { input := annotate text.toList 1 1 [] } with
  | .error e => .error e
  | .ok (es, _) => check file es

theorem parse_wellFormed {file text : String} {es : List Located}
    (h : parse file text = .ok es) : ∀ l ∈ es, Parser.wellFormed file l = true := by
  unfold parse at h
  split at h
  · cases h
  · exact Parser.check_ok h

theorem parse_line_pos {file text : String} {es : List Located}
    (h : parse file text = .ok es) : ∀ l ∈ es, 1 ≤ l.line := by
  intro l hl
  have := parse_wellFormed h l hl
  simp only [Parser.wellFormed, Bool.and_eq_true, decide_eq_true_eq] at this
  exact this.1.1

theorem parse_file_eq {file text : String} {es : List Located}
    (h : parse file text = .ok es) : ∀ l ∈ es, l.file = file := by
  intro l hl
  have := parse_wellFormed h l hl
  simp only [Parser.wellFormed, Bool.and_eq_true, beq_iff_eq] at this
  exact this.1.2

theorem parse_atom_safe {file text : String} {es : List Located}
    (h : parse file text = .ok es) :
    ∀ l ∈ es, ∀ c ∈ Parser.cmndAtoms l.entry, Parser.CmndAtom.pathOk c = true := by
  intro l hl c hc
  have hw := parse_wellFormed h l hl
  simp only [Parser.wellFormed, Bool.and_eq_true, List.all_eq_true] at hw
  exact hw.2 c hc

theorem parse_command_absolute {file text : String} {es : List Located}
    (h : parse file text = .ok es) :
    ∀ l ∈ es, ∀ p a, CmndAtom.command p a ∈ Parser.cmndAtoms l.entry →
      p.toList.head? = some '/' := by
  intro l hl p a hm
  simpa [Parser.CmndAtom.pathOk] using parse_atom_safe h l hl _ hm

theorem parse_digest_command_absolute {file text : String} {es : List Located}
    (h : parse file text = .ok es) :
    ∀ l ∈ es, ∀ ds p a, CmndAtom.digest ds (.command p a) ∈ Parser.cmndAtoms l.entry →
      p.toList.head? = some '/' := by
  intro l hl ds p a hm
  have hs := parse_atom_safe h l hl _ hm
  simp only [Parser.CmndAtom.pathOk, Bool.and_eq_true, beq_iff_eq] at hs
  exact hs.2

theorem parse_regex_anchored {file text : String} {es : List Located}
    (h : parse file text = .ok es) :
    ∀ l ∈ es, ∀ re a, CmndAtom.commandRegex re a ∈ Parser.cmndAtoms l.entry →
      re.startsWith "^" = true ∧ re.endsWith "$" = true := by
  intro l hl re a hm
  have hs := parse_atom_safe h l hl _ hm
  simpa [Parser.CmndAtom.pathOk] using hs

end LeanSudo.Sudoers
