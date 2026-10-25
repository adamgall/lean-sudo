import LeanSudo.I18n

namespace LeanSudo.I18n

private inductive Part where
  | literal (text : String)
  | argument (numeric : Bool)
  deriving Repr

private def parts : Nat → List Char → String → List Part
  | 0, _, literal => [.literal literal]
  | _ + 1, [], literal => [.literal literal]
  | fuel + 1, '%' :: '%' :: rest, literal => parts fuel rest (literal ++ "%")
  | fuel + 1, '%' :: rest, literal =>
    let flags := rest.takeWhile (fun c => c.isDigit || "-+ #.hljztL".contains c)
    match rest.drop flags.length with
    | c :: remaining =>
      if "scduioxX".contains c then
        .literal literal :: .argument (c != 's' && c != 'c') :: parts fuel remaining ""
      else parts fuel rest (literal ++ "%")
    | [] => [.literal (literal ++ "%" ++ String.ofList rest)]
  | fuel + 1, c :: rest, literal => parts fuel rest (literal.push c)

private def numeric (s : String) : Bool :=
  !s.isEmpty && s.toList.all (fun c => c.isDigit || "-+abcdefABCDEFxX".contains c)

private def capture : List Part → String → Option (List String)
  | [], text => if text.isEmpty then some [] else none
  | .literal initial :: rest, text =>
    if text.startsWith initial then capture rest (text.drop initial.length).toString else none
  | [.argument n], text => if !n || numeric text then some [text] else none
  | .argument n :: .literal separator :: rest, text => do
    if separator.isEmpty then
      if rest.isEmpty && (!n || numeric text) then some [text] else none
    else
      let chunks := text.splitOn separator
      if chunks.length < 2 then none else do
        let value := chunks.headD ""
        if n && !numeric value then none else do
          let remaining ← capture rest (separator.intercalate (chunks.drop 1))
          return value :: remaining
  | .argument _ :: _, _ => none

private def trimLine (s : String) : String :=
  String.ofList ((s.toList.reverse.dropWhile (· == '\n')).reverse)

private def score (ps : List Part) : Nat :=
  ps.foldl (fun n p => match p with | .literal s => n + s.length | _ => n) 0

private def renderTemplate (catalog : Catalog) (text : String) : String := Id.run do
  if text.isEmpty then return text
  let translated := lookup catalog text
  if translated != text then return translated
  let mut best := text
  let mut specificity := 2
  for (original, translation) in catalog.entries do
    let originals := original.splitOn "\x00"
    for original in originals do
      let original := trimLine original
      if !translation.isEmpty && !original.isEmpty && !original.contains '\n' then
        let ps := parts (original.length + 1) original.toList ""
        let weight := score ps
        if weight > specificity then
          if let some args := capture ps text then
            let translated := if originals.length > 1 then
                nlookup catalog (originals.headD "") (originals[1]!)
                  ((args.headD "0").toNat?.getD 0)
              else translation
            if translated != original then
              best := format (trimLine translated) args
              specificity := weight
          else if !original.contains '%' && original.endsWith ": " && text.startsWith original then
            best := translation ++ (text.drop original.length).toString
            specificity := weight
  return best

def renderMessage (catalog : Catalog) (text : String) : String := Id.run do
  let translated := renderTemplate catalog text
  if translated != text then return translated
  let fields := text.splitOn ": "
  for i in List.range (fields.length - 1) do
    let body := ": ".intercalate (fields.drop (i + 1))
    let translated := renderTemplate catalog body
    if translated != body then
      return ": ".intercalate (fields.take (i + 1)) ++ ": " ++ translated
  return text

def presentation (catalog : Catalog) : Catalog :=
  { catalog with entries := catalog.entries ++ catalog.entries.flatMap fun (source, target) =>
      if !source.contains '\n' || source.contains '\x00' then [] else
      let sources := source.splitOn "\n"
      let targets := target.splitOn "\n"
      if sources.length != targets.length then [] else
      (sources.zip targets).filter (fun pair => !pair.1.isEmpty && pair.1 != pair.2) }

def render (catalog : Catalog) (text : String) : String :=
  if text.isEmpty || catalog.entries.isEmpty then text else
  let exact := lookup catalog text
  if exact != text then exact else
  "\n".intercalate ((text.splitOn "\n").map fun line => Id.run do
    for initial in ["sudo: ", "sudoedit: ", "visudo: "] do
      if line.startsWith initial then
        return initial ++ renderMessage catalog (line.drop initial.length).toString
    return renderMessage catalog line)

end LeanSudo.I18n
