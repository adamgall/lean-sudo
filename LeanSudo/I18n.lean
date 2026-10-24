import Std

/-!
Pure GNU gettext catalogs. MO offsets and terminating NUL bytes are checked before
UTF-8 decoding; no input is executed. Plural expressions use the gettext integer
grammar with short-circuit evaluation. Invalid metadata uses the English rule.
`merge` keeps the first catalog's entries and each entry's own plural rule.
Formatting accepts string arguments only, never pointers or printf `%n`; unknown
or incomplete directives and missing arguments remain literal.
-/
namespace LeanSudo.I18n

inductive PluralExpr where
  | number (value : Int)
  | count
  | unary (op : Char) (arg : PluralExpr)
  | binary (op : String) (left right : PluralExpr)
  | cond (test yes no : PluralExpr)
  deriving Repr, BEq, Inhabited

private def truth (n : Int) : Int := if n == 0 then 0 else 1

/-- C/gettext integer arithmetic; division by zero is defined as zero. -/
def PluralExpr.eval : PluralExpr → Nat → Int
  | .number k, _ => k
  | .count, n => Int.ofNat n
  | .unary op x, n =>
    let v := x.eval n
    if op == '!' then if v == 0 then 1 else 0
    else if op == '-' then -v else v
  | .binary op x y, n =>
    let a := x.eval n
    if op == "&&" then if a == 0 then 0 else truth (y.eval n)
    else if op == "||" then if a != 0 then 1 else truth (y.eval n)
    else
      let b := y.eval n
      if op == "+" then a + b else if op == "-" then a - b
      else if op == "*" then a * b
      else if op == "/" then if b == 0 then 0 else a.tdiv b
      else if op == "%" then if b == 0 then 0 else a.tmod b
      else if op == "==" then if a == b then 1 else 0
      else if op == "!=" then if a != b then 1 else 0
      else if op == "<" then if a < b then 1 else 0
      else if op == "<=" then if a ≤ b then 1 else 0
      else if op == ">" then if a > b then 1 else 0
      else if op == ">=" then if a ≥ b then 1 else 0
      else 0
  | .cond p x y, n => if p.eval n != 0 then x.eval n else y.eval n

private def skipSpace (cs : List Char) : List Char := cs.dropWhile Char.isWhitespace

private def binaryOp : List Char → Option (String × Nat × List Char)
  | '|' :: '|' :: xs => some ("||", 2, xs)
  | '&' :: '&' :: xs => some ("&&", 3, xs)
  | '=' :: '=' :: xs => some ("==", 4, xs)
  | '!' :: '=' :: xs => some ("!=", 4, xs)
  | '<' :: '=' :: xs => some ("<=", 5, xs)
  | '>' :: '=' :: xs => some (">=", 5, xs)
  | '<' :: xs => some ("<", 5, xs)
  | '>' :: xs => some (">", 5, xs)
  | '+' :: xs => some ("+", 6, xs)
  | '-' :: xs => some ("-", 6, xs)
  | '*' :: xs => some ("*", 7, xs)
  | '/' :: xs => some ("/", 7, xs)
  | '%' :: xs => some ("%", 7, xs)
  | _ => none

mutual
  private def expression : Nat → Nat → List Char → Option (PluralExpr × List Char)
    | 0, _, _ => none
    | fuel + 1, prec, input => do
      let (first, rest) ← match skipSpace input with
        | '(' :: cs => do
          let (e, rest) ← expression fuel 1 cs
          match skipSpace rest with
          | ')' :: rest => pure (e, rest)
          | _ => none
        | 'n' :: cs => pure (.count, cs)
        | c :: cs =>
          if c == '!' || c == '+' || c == '-' then do
            let (e, rest) ← expression fuel 8 cs
            pure (.unary c e, rest)
          else if c.isDigit then do
            let digits := (c :: cs).takeWhile Char.isDigit
            let value ← (String.ofList digits).toNat?
            pure (.number (Int.ofNat value), (c :: cs).drop digits.length)
          else none
        | [] => none
      expressionTail fuel prec first rest
  private def expressionTail : Nat → Nat → PluralExpr → List Char →
      Option (PluralExpr × List Char)
    | 0, _, _, _ => none
    | fuel + 1, prec, left, input => do
      let rest := skipSpace input
      if prec ≤ 1 then
        match rest with
        | '?' :: cs =>
          let (yes, cs) ← expression fuel 1 cs
          let ':' :: cs := skipSpace cs | none
          let (no, cs) ← expression fuel 1 cs
          return (.cond left yes no, cs)
        | _ => pure ()
      match binaryOp rest with
      | some (op, level, cs) =>
        if level < prec then pure (left, rest)
        else do
          let (right, cs) ← expression fuel (level + 1) cs
          expressionTail fuel prec (.binary op left right) cs
      | none => pure (left, rest)
end

/-- Parse a complete gettext plural expression, rejecting trailing garbage. -/
def parsePlural (text : String) : Option PluralExpr := do
  let (e, rest) ← expression (text.length * 4 + 8) 1 text.toList
  if (skipSpace rest).isEmpty then some e else none

structure PluralRule where
  count : Nat := 2
  expr : PluralExpr := .binary "!=" .count (.number 1)
  deriving Repr, BEq, Inhabited

structure Catalog where
  /-- Raw MO originals/translations, including embedded plural NUL separators. -/
  entries : List (String × String) := []
  /-- Rules are keyed by the raw original, so catalog merging preserves locale rules. -/
  pluralRules : List (String × PluralRule) := []
  deriving Repr, BEq, Inhabited

private def singular (s : String) : String := (s.splitOn (String.singleton '\x00')).head!

private def entry (catalog : Catalog) (msgid : String) : Option (String × String) :=
  catalog.entries.find? (fun e => singular e.1 == msgid)

/-- Exact msgid fallback when no nonempty translation exists. -/
def lookup (catalog : Catalog) (msgid : String) : String :=
  match entry catalog msgid with
  | none => msgid
  | some (_, translated) =>
    let first := singular translated
    if first.isEmpty then msgid else first

/-- An absent catalog entry never changes the original diagnostic. -/
theorem lookup_absent (catalog : Catalog) (msgid : String)
    (h : catalog.entries.find? (fun e => singular e.1 == msgid) = none) :
    lookup catalog msgid = msgid := by
  simp [lookup, entry, h]

@[simp] theorem lookup_empty (msgid : String) : lookup {} msgid = msgid := by
  simp [lookup, entry]

/-- Missing/empty plural translations fall back to the original English forms. -/
def nlookup (catalog : Catalog) (msgid plural : String) (n : Nat) : String := Id.run do
  let fallback := if n == 1 then msgid else plural
  let some (original, translated) := entry catalog msgid | return fallback
  let rule := ((catalog.pluralRules.find? (fun r => r.1 == original)).map Prod.snd).getD {}
  let index := rule.expr.eval n
  if index < 0 || index.toNat ≥ rule.count then return fallback
  let some result := (translated.splitOn (String.singleton '\x00'))[index.toNat]?
    | return fallback
  return if result.isEmpty then fallback else result

/-- Left-biased catalog composition, retaining per-entry plural metadata. -/
def merge (preferred fallback : Catalog) : Catalog :=
  { entries := preferred.entries ++ fallback.entries
    pluralRules := preferred.entries.map (fun e =>
      (e.1, ((preferred.pluralRules.find? (fun r => r.1 == e.1)).map Prod.snd).getD {})) ++
      fallback.entries.map (fun e =>
      (e.1, ((fallback.pluralRules.find? (fun r => r.1 == e.1)).map Prod.snd).getD {})) }

private def trim (s : String) : String := s.trimAscii.toString

private def metadataRule (header : String) : PluralRule := Id.run do
  let some line := (header.splitOn "\n").find? (fun line =>
    ((line.splitOn ":").head!).toLower == "plural-forms") | return {}
  let fields := (String.intercalate ":" ((line.splitOn ":").drop 1)).splitOn ";"
  let fields := fields.map fun field => (field.splitOn "=").map trim
  let some countField := fields.find? (fun f => f.head! == "nplurals") | return {}
  let some count ← pure (countField[1]?.bind String.toNat?) | return {}
  if count == 0 then return {}
  let some exprField := fields.find? (fun f => f.head! == "plural") | return {}
  let some expr := parsePlural (String.intercalate "=" (exprField.drop 1)) | return {}
  return { count, expr }

private def word (bytes : ByteArray) (big : Bool) (offset : Nat) : Option Nat :=
  if offset + 4 ≤ bytes.size then
    let a := (bytes[offset]!).toNat
    let b := (bytes[offset + 1]!).toNat
    let c := (bytes[offset + 2]!).toNat
    let d := (bytes[offset + 3]!).toNat
    some (if big then ((a * 256 + b) * 256 + c) * 256 + d
      else ((d * 256 + c) * 256 + b) * 256 + a)
  else none

private def moString (bytes : ByteArray) (big : Bool) (descriptor : Nat) : Option String := do
  let length ← word bytes big descriptor
  let offset ← word bytes big (descriptor + 4)
  if offset + length < bytes.size && bytes[offset + length]! == 0 then
    String.fromUTF8? (bytes.extract offset (offset + length))
  else none

/-- Decode GNU MO revision-zero string tables in either byte order.
All descriptor/hash-table extents and string terminators must be within the file;
invalid UTF-8, unsupported revisions, and malformed tables are rejected. -/
def parseMo (bytes : ByteArray) : Option Catalog := do
  if bytes.size < 28 then none else do
    let magic ← word bytes false 0
    let big ← if magic == 0x950412de then some false
      else if magic == 0xde120495 then some true else none
    let revision ← word bytes big 4
    if revision != 0 then none else do
      let count ← word bytes big 8
      let originals ← word bytes big 12
      let translations ← word bytes big 16
      let hashes ← word bytes big 20
      let hashOffset ← word bytes big 24
      if originals + count * 8 > bytes.size || translations + count * 8 > bytes.size ||
          (hashes != 0 && hashOffset + hashes * 4 > bytes.size) then none else do
        let entries ← (List.range count).mapM fun i => do
          let original ← moString bytes big (originals + i * 8)
          let translated ← moString bytes big (translations + i * 8)
          pure (original, translated)
        let header := ((entries.find? (fun e => e.1.isEmpty)).map Prod.snd).getD ""
        let rule := metadataRule header
        pure { entries, pluralRules := entries.map (fun e => (e.1, rule)) }

private structure Spec where
  position : Option Nat
  flags : List Char
  width : Nat
  precision : Option Nat
  conversion : Char

private def spec (input : List Char) : Option (Spec × List Char) := do
  let digits := input.takeWhile Char.isDigit
  let afterDigits := input.drop digits.length
  let (position, rest) ← match afterDigits with
    | '$' :: cs => do
      let n ← (String.ofList digits).toNat?
      if n == 0 then none else pure (some (n - 1), cs)
    | _ => pure (none, input)
  let flags := rest.takeWhile (fun c => ['-', '+', ' ', '0', '#'].contains c)
  let rest := rest.drop flags.length
  let widthDigits := rest.takeWhile Char.isDigit
  let width := ((String.ofList widthDigits).toNat?).getD 0
  -- Bound padding allocation for untrusted catalog directives.
  if width > 65536 then none else do
    let rest := rest.drop widthDigits.length
    let (precision, rest) := match rest with
      | '.' :: cs =>
        let ds := cs.takeWhile Char.isDigit
        (some (((String.ofList ds).toNat?).getD 0), cs.drop ds.length)
      | _ => (none, rest)
    if precision.getD 0 > 65536 then none else do
      let rest := match rest with
        | 'h' :: 'h' :: cs | 'l' :: 'l' :: cs => cs
        | 'h' :: cs | 'l' :: cs | 'j' :: cs | 'z' :: cs | 't' :: cs | 'L' :: cs => cs
        | _ => rest
      let c :: rest := rest | none
      if ['s', 'c', 'd', 'u', 'i', 'o', 'x', 'X'].contains c then
        pure ({ position, flags, width, precision, conversion := c }, rest)
      else none

private def repeatChar (c : Char) (n : Nat) : String := String.ofList (List.replicate n c)

private def render (s : Spec) (argument : String) : String := Id.run do
  let numeric := s.conversion != 's' && s.conversion != 'c'
  let mut value := argument
  if numeric then
    let chars := value.toList
    let (sign, digits) := match chars with
      | '-' :: cs => ("-", String.ofList cs)
      | '+' :: cs => ("+", String.ofList cs)
      | _ => (if s.flags.contains '+' then "+" else if s.flags.contains ' ' then " " else "", value)
    let digits := if s.precision == some 0 && digits == "0" then "" else digits
    value := sign ++ repeatChar '0' (s.precision.getD 0 - digits.length) ++ digits
  else
    if let some precision := s.precision then value := String.ofList (value.toList.take precision)
  let padding := s.width - value.length
  if s.flags.contains '-' then return value ++ repeatChar ' ' padding
  if numeric && s.flags.contains '0' && s.precision.isNone then
    match value.toList with
    | c :: cs =>
      if c == '-' || c == '+' || c == ' ' then
        return String.singleton c ++ repeatChar '0' padding ++ String.ofList cs
      else return repeatChar '0' padding ++ value
    | [] => return repeatChar '0' padding
  return repeatChar ' ' padding ++ value

private def formatParts : Nat → List Char → Array String → Nat → List String
  | 0, cs, _, _ => [String.ofList cs]
  | fuel + 1, cs, args, next =>
    let literal := cs.takeWhile (· != '%')
    match cs.drop literal.length with
    | [] => [String.ofList literal]
    | '%' :: '%' :: rest => String.ofList literal :: "%" :: formatParts fuel rest args next
    | '%' :: rest =>
      match spec rest with
      | none => String.ofList literal :: "%" :: formatParts fuel rest args next
      | some (s, remaining) =>
        let raw := "%" ++ String.ofList (rest.take (rest.length - remaining.length))
        let replacement := (args[s.position.getD next]?).map (render s) |>.getD raw
        String.ofList literal :: replacement ::
          formatParts fuel remaining args (if s.position.isSome then next else next + 1)
    | _ => [String.ofList cs]

/-- Safe printf-style substitution: `%s`, `%c`, integer conversions, `%%`,
positional arguments, flags, static width/precision and integer length modifiers. Values are
already-rendered strings. Unsupported directives are preserved, not interpreted. -/
def format (template : String) (args : List String) : String :=
  String.join (formatParts (template.length + 1) template.toList args.toArray 0)

end LeanSudo.I18n
