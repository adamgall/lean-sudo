import LeanSudo.Sys.Prim.CoreLogs

namespace LeanSudo.Sys.TimeFormat

private abbrev P := Prim.CoreLogs.TimeFields

private def byteText (bytes : ByteArray) : String :=
  String.ofList (bytes.data.toList.map fun byte => Char.ofNat byte.toNat)

private def textBytes (text : String) : ByteArray :=
  ⟨text.toList.toArray.map fun c => c.toNat.toUInt8⟩

private def locale (item : UInt32) : IO String := do
  return byteText (← Prim.CoreLogs.langinfo item 65536)

private def dayItem (full : Bool) (index : Nat) : UInt32 :=
  if full then
    match index with
    | 0 => Prim.CoreLogs.DAY_1 ()
    | 1 => Prim.CoreLogs.DAY_2 ()
    | 2 => Prim.CoreLogs.DAY_3 ()
    | 3 => Prim.CoreLogs.DAY_4 ()
    | 4 => Prim.CoreLogs.DAY_5 ()
    | 5 => Prim.CoreLogs.DAY_6 ()
    | _ => Prim.CoreLogs.DAY_7 ()
  else
    match index with
    | 0 => Prim.CoreLogs.ABDAY_1 ()
    | 1 => Prim.CoreLogs.ABDAY_2 ()
    | 2 => Prim.CoreLogs.ABDAY_3 ()
    | 3 => Prim.CoreLogs.ABDAY_4 ()
    | 4 => Prim.CoreLogs.ABDAY_5 ()
    | 5 => Prim.CoreLogs.ABDAY_6 ()
    | _ => Prim.CoreLogs.ABDAY_7 ()

private def monthItem (full alternate : Bool) (index : Nat) : UInt32 :=
  match full, alternate with
  | true, false =>
    match index with
    | 0 => Prim.CoreLogs.MON_1 ()
    | 1 => Prim.CoreLogs.MON_2 ()
    | 2 => Prim.CoreLogs.MON_3 ()
    | 3 => Prim.CoreLogs.MON_4 ()
    | 4 => Prim.CoreLogs.MON_5 ()
    | 5 => Prim.CoreLogs.MON_6 ()
    | 6 => Prim.CoreLogs.MON_7 ()
    | 7 => Prim.CoreLogs.MON_8 ()
    | 8 => Prim.CoreLogs.MON_9 ()
    | 9 => Prim.CoreLogs.MON_10 ()
    | 10 => Prim.CoreLogs.MON_11 ()
    | _ => Prim.CoreLogs.MON_12 ()
  | false, false =>
    match index with
    | 0 => Prim.CoreLogs.ABMON_1 ()
    | 1 => Prim.CoreLogs.ABMON_2 ()
    | 2 => Prim.CoreLogs.ABMON_3 ()
    | 3 => Prim.CoreLogs.ABMON_4 ()
    | 4 => Prim.CoreLogs.ABMON_5 ()
    | 5 => Prim.CoreLogs.ABMON_6 ()
    | 6 => Prim.CoreLogs.ABMON_7 ()
    | 7 => Prim.CoreLogs.ABMON_8 ()
    | 8 => Prim.CoreLogs.ABMON_9 ()
    | 9 => Prim.CoreLogs.ABMON_10 ()
    | 10 => Prim.CoreLogs.ABMON_11 ()
    | _ => Prim.CoreLogs.ABMON_12 ()
  | true, true =>
    match index with
    | 0 => Prim.CoreLogs.ALTMON_1 ()
    | 1 => Prim.CoreLogs.ALTMON_2 ()
    | 2 => Prim.CoreLogs.ALTMON_3 ()
    | 3 => Prim.CoreLogs.ALTMON_4 ()
    | 4 => Prim.CoreLogs.ALTMON_5 ()
    | 5 => Prim.CoreLogs.ALTMON_6 ()
    | 6 => Prim.CoreLogs.ALTMON_7 ()
    | 7 => Prim.CoreLogs.ALTMON_8 ()
    | 8 => Prim.CoreLogs.ALTMON_9 ()
    | 9 => Prim.CoreLogs.ALTMON_10 ()
    | 10 => Prim.CoreLogs.ALTMON_11 ()
    | _ => Prim.CoreLogs.ALTMON_12 ()
  | false, true =>
    match index with
    | 0 => Prim.CoreLogs.ABALTMON_1 ()
    | 1 => Prim.CoreLogs.ABALTMON_2 ()
    | 2 => Prim.CoreLogs.ABALTMON_3 ()
    | 3 => Prim.CoreLogs.ABALTMON_4 ()
    | 4 => Prim.CoreLogs.ABALTMON_5 ()
    | 5 => Prim.CoreLogs.ABALTMON_6 ()
    | 6 => Prim.CoreLogs.ABALTMON_7 ()
    | 7 => Prim.CoreLogs.ABALTMON_8 ()
    | 8 => Prim.CoreLogs.ABALTMON_9 ()
    | 9 => Prim.CoreLogs.ABALTMON_10 ()
    | 10 => Prim.CoreLogs.ABALTMON_11 ()
    | _ => Prim.CoreLogs.ABALTMON_12 ()

private def field (time : P) (index : Nat) : Int := time.fields[index]!.toInt

private def leap (year : Int) : Bool :=
  year % 4 == 0 && (year % 100 != 0 || year % 400 == 0)

private def weeks (year jan1 : Int) : Int :=
  if jan1 == 4 || (jan1 == 3 && leap year) then 53 else 52

private def isoWeek (time : P) : Int × Int := Id.run do
  let year := field time 5 + 1900
  let day := field time 7
  let weekday := (field time 6 + 6) % 7 + 1
  let jan1 := (field time 6 - day) % 7
  let week := (day + 11 - weekday) / 7
  if week == 0 then
    let previous := year - 1
    return (previous, weeks previous ((jan1 - if leap previous then 2 else 1) % 7))
  if week > weeks year jan1 then return (year + 1, 1)
  return (year, week)

private structure Era where
  name : String
  format : String
  year : Int

private def dateValue (value : String) : Option (Int × Int) := do
  let [year, month, day] := value.splitOn "/" | none
  let year ← year.toInt?
  let month ← month.toInt?
  let day ← day.toInt?
  return (year, year * 10000 + month * 100 + day)

private def eraFor (time : P) : IO (Option Era) := do
  let year := field time 5 + 1900
  let date := year * 10000 + (field time 4 + 1) * 100 + field time 3
  let entries ← locale (Prim.CoreLogs.ERA ())
  for entry in entries.splitOn ";" do
    let parts := entry.splitOn ":"
    if parts.length >= 6 then
      let direction := parts[0]!
      if let some offset := parts[1]!.toInt? then
        if let some (startYear, start) := dateValue parts[2]! then
          let finish := parts[3]!
          let inRange : Bool := if finish == "+*" then date >= start
            else if finish == "-*" then date <= start
            else match dateValue finish with
              | some (_, stop) => min start stop <= date && date <= max start stop
              | none => false
          if inRange then
            return some {
              name := parts[4]!
              format := String.intercalate ":" (parts.drop 5)
              year := offset + (if direction == "-" then startYear - year else year - startYear) }
  return none

private def pad (value : String) (width : Nat) (fill : Char) : String :=
  String.ofList (List.replicate (width - value.length) fill) ++ value

private def number (value : Int) (width : Nat) (fill : Char) : String :=
  if value < 0 && fill == '0' then "-" ++ pad (toString value.natAbs) (width - 1) fill
  else pad (toString value) width fill

private def caseText (text : String) (upper : Bool) : IO String := do
  let mut bytes := ByteArray.empty
  for c in text.toList do
    let value ← if upper then Prim.CoreLogs.upperByte c.toNat.toUInt32
      else Prim.CoreLogs.lowerByte c.toNat.toUInt32
    bytes := bytes.push value.toUInt8
  return byteText bytes

private structure Directive where
  flag : Char := ' '
  width : Option Nat := none
  upper : Bool := false
  swap : Bool := false
  modifier : Char := ' '
  code : Char := ' '
  original : String := "%"
  deriving Inhabited

private partial def parseDirective (chars : List Char) : Directive × List Char := Id.run do
  let mut rest := chars
  let mut directive : Directive := {}
  repeat
    let flag :: next := rest | break
    if flag == '_' || flag == '-' || flag == '0' then
      directive := { directive with flag, original := directive.original.push flag }
    else if flag == '^' then
      directive := { directive with upper := true, original := directive.original.push flag }
    else if flag == '#' then
      directive := { directive with swap := true, original := directive.original.push flag }
    else break
    rest := next
  let digits := rest.takeWhile Char.isDigit
  if !digits.isEmpty then
    directive := { directive with
      width := (String.ofList digits).toNat?
      original := directive.original ++ String.ofList digits }
    rest := rest.drop digits.length
  if let modifier :: next := rest then
    if modifier == 'E' || modifier == 'O' then
      directive := { directive with modifier, original := directive.original.push modifier }
      rest := next
  if let code :: next := rest then
    return ({ directive with code, original := directive.original.push code }, next)
  return (directive, [])

private def numeric (directive : Directive) (value : Int) (width : Nat)
    (fill : Char := '0') : IO String := do
  if directive.modifier == 'O' && value >= 0 then
    let digits := (← locale (Prim.CoreLogs.ALT_DIGITS ())).splitOn ";"
    if let some alternative := digits[value.toNat]? then
      unless alternative.isEmpty do return alternative
  let fill := if directive.flag == '_' then ' ' else if directive.flag == '0' then '0' else fill
  let width := if directive.flag == '-' then 0 else max width (directive.width.getD 0)
  return number value width fill

private def validModifier (directive : Directive) : Bool :=
  if directive.modifier == 'E' then !"%aAbBhDdeFHIlkjMmSUVgGWw".contains directive.code
  else if directive.modifier == 'O' then !"%aAcxXDFY".contains directive.code
  else true

private partial def render (format : String) (time : P) : IO String := do
  let mut rest := format.toList
  let mut out := ""
  repeat
    let c :: next := rest | break
    rest := next
    if c != '%' then
      out := out.push c
      continue
    let (directive, next) := parseDirective rest
    rest := next
    let code := directive.code
    if !validModifier directive || code == ' ' then
      out := out ++ directive.original
      continue
    let year := field time 5 + 1900
    let numericResult := "CdyYeHkIlmMSjwuUWVgGs".contains code
    let mut value ← match code with
      | '%' => pure "%"
      | 'n' => pure "\n"
      | 't' => pure "\t"
      | 'a' | 'A' => locale (dayItem (code == 'A') (field time 6).toNat)
      | 'b' | 'B' | 'h' =>
        locale (monthItem (code == 'B') (directive.modifier == 'O') (field time 4).toNat)
      | 'p' | 'P' => do
        let value ← locale
          (if field time 2 < 12 then Prim.CoreLogs.AM_STR () else Prim.CoreLogs.PM_STR ())
        if code == 'P' then caseText value false else pure value
      | 'Z' => pure (byteText time.zone)
      | 'z' => do
        if field time 8 < 0 then pure ""
        else
          let offset := time.offset.toInt
          let value ← numeric directive (offset.natAbs / 3600 * 100 + offset.natAbs / 60 % 60) 4
          pure ((if offset < 0 then "-" else "+") ++ value)
      | 'c' | 'x' | 'X' | 'r' => do
        let item := if code == 'c' then Prim.CoreLogs.D_T_FMT ()
          else if code == 'x' then Prim.CoreLogs.D_FMT ()
          else if code == 'X' then Prim.CoreLogs.T_FMT () else Prim.CoreLogs.T_FMT_AMPM ()
        let mut format ← locale item
        if code == 'r' && format.isEmpty then format := "%I:%M:%S %p"
        if directive.modifier == 'E' && code != 'r' then
          let alternative ← locale (if code == 'c' then Prim.CoreLogs.ERA_D_T_FMT ()
            else if code == 'x' then Prim.CoreLogs.ERA_D_FMT () else Prim.CoreLogs.ERA_T_FMT ())
          unless alternative.isEmpty do format := alternative
        render format time
      | 'D' => render "%m/%d/%y" time
      | 'F' => render "%Y-%m-%d" time
      | 'R' => render "%H:%M" time
      | 'T' => render "%H:%M:%S" time
      | 'C' | 'y' | 'Y' => do
        if directive.modifier == 'E' then
          if let some era ← eraFor time then
            if code == 'C' then return era.name
            if code == 'Y' then return ← render era.format time
            return ← numeric directive era.year 2
        let value := if code == 'C' then year / 100 else if code == 'y' then year % 100 else year
        numeric directive value (if code == 'y' then 2 else 1)
      | 'd' | 'e' => do
        numeric directive (field time 3) 2 (if code == 'e' then ' ' else '0')
      | 'H' | 'k' => do
        numeric directive (field time 2) 2 (if code == 'k' then ' ' else '0')
      | 'I' | 'l' => do
        let hour := field time 2 % 12
        numeric directive (if hour == 0 then 12 else hour) 2 (if code == 'l' then ' ' else '0')
      | 'm' => numeric directive (field time 4 + 1) 2
      | 'M' => numeric directive (field time 1) 2
      | 'S' => numeric directive (field time 0) 2
      | 'j' => numeric directive (field time 7 + 1) 3
      | 'w' => numeric directive (field time 6) 1
      | 'u' => numeric directive ((field time 6 + 6) % 7 + 1) 1
      | 'U' => numeric directive ((field time 7 + 7 - field time 6) / 7) 2
      | 'W' => numeric directive ((field time 7 + 7 - (field time 6 + 6) % 7) / 7) 2
      | 'V' => numeric directive (isoWeek time).2 2
      | 'g' => numeric directive ((isoWeek time).1 % 100) 2
      | 'G' => numeric directive (isoWeek time).1 1
      | 's' => do
        numeric { directive with modifier := ' ' } (← Prim.CoreLogs.mktime time.fields).toInt 1
      | _ => pure directive.original
    if directive.upper || (directive.swap && "aAbBh".contains code) then
      value ← caseText value true
    else if directive.swap && "pPZ".contains code then value ← caseText value false
    if !numericResult && directive.flag != '-' then
      if let some width := directive.width then
        value := pad value width (if directive.flag == '0' then '0' else ' ')
    out := out ++ value
  return out

def format (format : String) (time : Prim.CoreLogs.TimeFields) : IO ByteArray := do
  return textBytes (← render (byteText format.toUTF8) time)

end LeanSudo.Sys.TimeFormat
