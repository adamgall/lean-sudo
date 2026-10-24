import LeanSudo.Sudoers.Ast

/-!
# sudoers parser

A scannerless recursive-descent parser for the subset of the sudoers(5) grammar that
lean-sudo implements. It follows the lexical rules of sudo's `toke.l` where feasible
(comments, `#uid`, line continuation, `WORD` characters, command argument escapes) and
is **fail-closed**: every construct whose semantics the policy engine does not
implement is a parse error.

Termination: every loop runs over a bounded range of `input length + 1` iterations and
each iteration consumes at least one character (or exits); running out of iterations
is reported as an error rather than silently truncating the input.

`parse` finally re-checks structural invariants of its result (`Located.wellFormed`);
the theorems at the end of this file are stated about `parse` itself.
-/

namespace LeanSudo.Sudoers

/-- A sudoers syntax error with a 1-based line and column. -/
structure ParseError where
  file : String
  line : Nat
  col : Nat
  msg : String
  deriving Repr, BEq, Inhabited

/-- `<file>:<line>:<col>: syntax error[: detail]` (sudo 1.9 style). -/
def ParseError.toString (e : ParseError) : String :=
  s!"{e.file}:{e.line}:{e.col}: syntax error" ++ (if e.msg.isEmpty then "" else s!": {e.msg}")

instance : ToString ParseError := ⟨ParseError.toString⟩

namespace Parser

/-- A character with its 1-based source position. -/
structure PChar where
  c : Char
  line : Nat
  col : Nat
  deriving Repr, Inhabited

/-- Attach positions (tail-recursive: sudoers files can be large). -/
def annotate : List Char → Nat → Nat → List PChar → List PChar
  | [], _, _, acc => acc.reverse
  | c :: cs, l, k, acc =>
    if c == '\n' then annotate cs (l + 1) 1 (⟨c, l, k⟩ :: acc)
    else annotate cs l (k + 1) (⟨c, l, k⟩ :: acc)

/-- Position just past the last character. -/
def endPos : List Char → Nat → Nat → Nat × Nat
  | [], l, k => (l, k)
  | c :: cs, l, k => if c == '\n' then endPos cs (l + 1) 1 else endPos cs l (k + 1)

structure Ctx where
  file : String
  eofLine : Nat
  eofCol : Nat
  /-- Iteration bound for every loop: one more than the input length. Each loop
  iteration consumes at least one character or exits, so this is never exhausted. -/
  fuel : Nat

abbrev P := ReaderT Ctx (StateT (List PChar) (Except ParseError))

/-! ## Character classes -/

def isBlank (c : Char) : Bool := c == ' ' || c == '\t' || c == '\r'

/-- sudo's `WORD` characters (excluding escapes). -/
def isWordChar (c : Char) : Bool :=
  !(isBlank c || c == '\n' || c == '#' || c == '>' || c == '!' || c == '=' || c == ':' ||
    c == ',' || c == '(' || c == ')' || c == '"' || c == '\\')

def isAliasName (s : String) : Bool :=
  match s.toList with
  | c :: cs => c.isUpper && cs.all (fun d => d.isUpper || d.isDigit || d == '_')
  | [] => false

def isTagChar (c : Char) : Bool := c.isUpper || c == '_'

/-- After a backslash: is this a line continuation (`[[:blank:]]*\n`)? -/
def isCont : List PChar → Bool
  | [] => false
  | c :: cs => if c.c == '\n' then true else if isBlank c.c then isCont cs else false

/-- Skip blanks and line continuations. `inCont`: inside a continuation, before its newline. -/
def skipWsAux : Bool → List PChar → List PChar
  | _, [] => []
  | false, c :: cs =>
    if isBlank c.c then skipWsAux false cs
    else if c.c == '\\' && isCont cs then skipWsAux true cs
    else c :: cs
  | true, c :: cs => if c.c == '\n' then skipWsAux false cs else skipWsAux true cs

/-- Does the input start with `s`? Returns the rest. -/
def stripPrefix : List PChar → List Char → Option (List PChar)
  | inp, [] => some inp
  | c :: cs, d :: ds => if c.c == d then stripPrefix cs ds else none
  | [], _ :: _ => none

/-- Uppercase keyword (`[A-Z_]+`) followed by optional blanks and a separator char. -/
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

/-! ## Primitive parsers -/

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

/-- sudo `WORD`: returns the unescaped text and whether any escape was used. -/
def readWord : P (String × Bool) := do
  let mut acc : List Char := []
  let mut esc := false
  for _ in [0:(← fuel)] do
    match (← get) with
    | c :: cs =>
      if c.c == '\\' then
        match cs with
        | d :: ds =>
          if d.c == '\n' || d.c == '\t' || isCont cs then break
          set ds
          esc := true
          acc := d.c :: acc
        | [] => break
      else if isWordChar c.c then
        set cs
        acc := c.c :: acc
      else break
    | [] => break
  return (String.ofList acc.reverse, esc)

/-- Double-quoted string (current char is `"`); `\c` → `c`, continuations removed. -/
def readQuoted : P String := do
  expect '"'
  let mut acc : List Char := []
  for _ in [0:(← fuel)] do
    match (← get) with
    | [] => err "unterminated quoted string"
    | c :: cs =>
      if c.c == '"' then
        set cs
        return String.ofList acc.reverse
      else if c.c == '\n' then err "unterminated quoted string"
      else if c.c == '\\' then
        if isCont cs then set (skipWsAux false (c :: cs))
        else
          match cs with
          | d :: ds =>
            set ds
            acc := d.c :: acc
          | [] => err "unterminated quoted string"
      else
        set cs
        acc := c.c :: acc
  err "unterminated quoted string"

/-- Decimal number (for `#uid` / `%#gid`); must not run into a word character. -/
def readNat : P Nat := do
  let mut n := 0
  let mut any := false
  for _ in [0:(← fuel)] do
    match (← peek) with
    | some c =>
      if c.isDigit then
        advance
        n := n * 10 + (c.toNat - '0'.toNat)
        any := true
      else break
    | none => break
  if !any then err "expected a numeric id"
  match (← peek) with
  | some c => if isWordChar c || c == '\\' then err "invalid numeric id" else pure n
  | none => pure n

/-- Negation prefix: `!`* (blanks allowed); returns the number of `!`. -/
def negCount : P Nat := do
  let mut n := 0
  for _ in [0:(← fuel)] do
    ws
    if (← peek) == some '!' then
      advance
      n := n + 1
    else break
  return n

def member (atom : P α) : P (Member α) := do
  let n ← negCount
  let a ← atom
  return ⟨n % 2 == 1, a⟩

/-- `item (, item)*` with optional blanks around the commas. -/
def list1 (item : P α) : P (List α) := do
  let mut acc := [← item]
  for _ in [0:(← fuel)] do
    ws
    if (← peek) == some ',' then
      advance
      ws
      acc := (← item) :: acc
    else return acc.reverse
  err "list too long"

/-! ## Atoms -/

def userAtom : P UserAtom := do
  match (← peek) with
  | some '#' =>
    advance
    return .id (← readNat)
  | some '%' =>
    advance
    match (← peek) with
    | some ':' => err "non-Unix groups (%:group) are not supported"
    | some '#' =>
      advance
      return .gid (← readNat)
    | some '"' => return .group (← readQuoted)
    | p =>
      let (w, _) ← readWord
      if w.isEmpty then err s!"expected a group name, found {describe p}"
      return .group w
  | some '+' => err "netgroups are not supported"
  | some '"' => return .name (← readQuoted)
  | p =>
    let pos ← curPos
    let (w, esc) ← readWord
    if w.isEmpty then errAt pos s!"expected a user name, found {describe p}"
    if !esc && w == "ALL" then return .all
    if !esc && isAliasName w then return .alias w
    return .name w

/-- Only digits, dots and glob characters, with a dot: looks like an IPv4 address. -/
def looksLikeIPv4 (s : String) : Bool :=
  s.toList.contains '.' &&
    s.toList.all (fun c => c.isDigit || c == '.' || c == '*' || c == '?' || c == '[' || c == ']')

def hostAtom : P HostAtom := do
  match (← peek) with
  | some '+' => err "netgroups are not supported"
  | p =>
    let pos ← curPos
    let (w, esc) ← readWord
    if w.isEmpty then errAt pos s!"expected a host name, found {describe p}"
    if !esc && w == "ALL" then return .all
    if !esc && isAliasName w then return .alias w
    if w.toList.contains '/' || w.toList.contains ':' || looksLikeIPv4 w then
      errAt pos s!"IP addresses and network masks are not supported: {w}"
    return .name w

def isCmdTerminator (c : Char) : Bool :=
  isBlank c || c == '\n' || c == '#' || c == ':' || c == ','

/-- A command path (`isPath`) or argument word, with sudo's command escapes:
`\*` `\?` `\[` `\]` `\!` `\^` are kept verbatim (glob escapes for fnmatch);
`\:` `\\` `\,` `\=` `\ ` `\t` `\#` lose the backslash. -/
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
          else if d.c == ':' || d.c == '\\' || d.c == ',' || d.c == '=' || d.c == ' ' ||
              d.c == '\t' || d.c == '#' then
            set ds
            acc := d.c :: acc
          else err s!"invalid escape sequence '\\{d.c}' in command"
        | [] => err "invalid escape at end of file"
      else if isCmdTerminator c.c || (isPath && c.c == '=') then break
      else
        set cs
        acc := c.c :: acc
  return String.ofList acc.reverse

/-- Command arguments up to the next unescaped `,` `:` `#` or end of line. -/
def cmndArgs : P CmndArgs := do
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
    if s.startsWith "^" && s.endsWith "$" then
      err "regular expressions in command arguments are not supported"
    return .pattern s

def digestPrefixes : List String := ["sha224:", "sha256:", "sha384:", "sha512:"]

/-- A command atom; `allowArgs = false` in `Defaults!` lists. -/
def cmndAtom (allowArgs : Bool) : P CmndAtom := do
  let inp ← get
  if digestPrefixes.any (fun d => (stripPrefix inp d.toList).isSome) then
    err "command digests are not supported"
  match (← peek) with
  | some '/' =>
    let p ← readCmdWord true
    let args ← if allowArgs then cmndArgs else pure .any
    return .command p args
  | some '^' => err "regular expressions are not supported"
  | p =>
    let pos ← curPos
    let (w, esc) ← readWord
    if w.isEmpty then errAt pos s!"expected a command, found {describe p}"
    if !esc && w == "ALL" then return .all
    if !esc && isAliasName w then return .alias w
    if w == "sudoedit" then
      return .sudoedit (← if allowArgs then cmndArgs else pure .any)
    if w == "list" then errAt pos "the \"list\" pseudo-command is not supported"
    errAt pos s!"expected a fully-qualified path name, found \"{w}\""

/-! ## Command specifications -/

def runasSpec : P RunasSpec := do
  expect '('
  ws
  match (← peek) with
  | some ')' =>
    advance
    return { users := none, groups := none }
  | some ':' =>
    advance
    ws
    if (← peek) == some ')' then
      advance
      return { users := none, groups := none }
    let g ← list1 (member userAtom)
    ws
    expect ')'
    return { users := none, groups := some g }
  | _ =>
    let u ← list1 (member userAtom)
    ws
    if (← peek) == some ':' then
      advance
      ws
      let g ← list1 (member userAtom)
      ws
      expect ')'
      return { users := some u, groups := some g }
    expect ')'
    return { users := some u, groups := none }

/-- State inherited between the commands of one `Cmnd_Spec_List`. -/
structure Inherit where
  runas : Option RunasSpec := none
  options : CmndOptions := {}
  tags : Tags := {}

def unsupportedOptions : List String :=
  ["CHROOT", "TIMEOUT", "NOTBEFORE", "NOTAFTER", "ROLE", "TYPE", "APPARMOR_PROFILE",
   "PRIVS", "LIMITPRIVS"]

def droppedTags : List String :=
  ["EXEC", "NOINTERCEPT", "MAIL", "NOMAIL", "FOLLOW", "NOFOLLOW", "LOG_INPUT",
   "NOLOG_INPUT", "LOG_OUTPUT", "NOLOG_OUTPUT"]

def unsupportedTags : List String := ["NOEXEC", "INTERCEPT"]

def cwdValue : P (Option String) := do
  ws
  let pos ← curPos
  let p ← peek
  let (w, _) ← readWord
  if w == "*" then return none
  if w.startsWith "/" then return some w
  if w.isEmpty then errAt pos s!"expected a directory for CWD, found {describe p}"
  errAt pos s!"CWD must be a fully-qualified path or *: {w}"

def cmndSpec (inh : Inherit) : P (CmndSpec × Inherit) := do
  ws
  let mut runas := inh.runas
  if (← peek) == some '(' then
    runas := some (← runasSpec)
  let mut options := inh.options
  for _ in [0:(← fuel)] do
    ws
    match kwAux (← get) [] with
    | some (w, '=', rest) =>
      if w == "CWD" then
        set rest
        options := { options with cwd := some (← cwdValue) }
      else if unsupportedOptions.contains w then err s!"the {w} option is not supported"
      else break
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
      else if droppedTags.contains w then pure ()
      else if unsupportedTags.contains w then err s!"the {w} tag is not supported"
      else break
      set rest
    | _ => break
  let cmnd ← member (cmndAtom true)
  return ({ runas, options, tags, cmnd }, { runas, options, tags })

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

def userSpec : P UserSpec := do
  let users ← list1 (member userAtom)
  ws
  let mut entries := [← hostCmnds]
  for _ in [0:(← fuel)] do
    ws
    if (← peek) == some ':' then
      advance
      ws
      entries := (← hostCmnds) :: entries
    else return { users, entries := entries.reverse }
  err "user specification too long"

/-! ## Aliases and Defaults -/

def aliasName : P String := do
  ws
  let pos ← curPos
  let p ← peek
  let (w, esc) ← readWord
  if w.isEmpty then errAt pos s!"expected an alias name, found {describe p}"
  if esc || !isAliasName w then errAt pos s!"invalid alias name \"{w}\""
  if w == "ALL" then
    errAt pos "\"ALL\" is a reserved word and cannot be used as an alias name"
  return w

/-- `NAME = list (: NAME = list)*` -/
def aliasDefs (item : P α) : P (List (String × List α)) := do
  let name ← aliasName
  ws
  expect '='
  ws
  let mut acc := [(name, ← list1 item)]
  for _ in [0:(← fuel)] do
    ws
    if (← peek) == some ':' then
      advance
      let name ← aliasName
      ws
      expect '='
      ws
      acc := (name, ← list1 item) :: acc
    else return acc.reverse
  err "alias definition too long"

/-- Bare Defaults value (sudo `ENVAR`): no `"` `!` `=` `,` or blanks; `\c` → `c`. -/
def bareValue : P String := do
  let mut acc : List Char := []
  for _ in [0:(← fuel)] do
    match (← get) with
    | [] => break
    | c :: cs =>
      if c.c == '\\' then
        if isCont cs then break
        match cs with
        | d :: ds =>
          set ds
          acc := d.c :: acc
        | [] => break
      else if isBlank c.c || c.c == '\n' || c.c == '"' || c.c == '!' || c.c == '=' ||
          c.c == ',' || (acc.isEmpty && c.c == ':') then break
      else
        set cs
        acc := c.c :: acc
  if acc.isEmpty then err "missing value"
  return String.ofList acc.reverse

def defaultsValue : P String := do
  ws
  if (← peek) == some '"' then readQuoted else bareValue

def readName : P String := do
  let mut acc : List Char := []
  for _ in [0:(← fuel)] do
    match (← peek) with
    | some c =>
      if c.isAlphanum || c == '_' then
        advance
        acc := c :: acc
      else break
    | none => break
  return String.ofList acc.reverse

def defaultsSetting : P DefaultsSetting := do
  let n ← negCount
  let pos ← curPos
  let p ← peek
  let name ← readName
  if name.isEmpty then errAt pos s!"expected a Defaults setting, found {describe p}"
  ws
  let withValue (mk : String → DefaultsOp) : P DefaultsSetting := do
    if n != 0 then errAt pos s!"negated Defaults setting \"{name}\" cannot take a value"
    return { name, op := mk (← defaultsValue) }
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
  | _, _ => return { name, op := .flag (n % 2 == 0) }

/-- After the `Defaults` keyword. -/
def defaultsEntry : P Entry := do
  let scope ← match (← peek) with
    | some '@' => do advance; ws; pure (DefaultsScope.host (← list1 (member hostAtom)))
    | some ':' => do advance; ws; pure (DefaultsScope.user (← list1 (member userAtom)))
    | some '>' => do advance; ws; pure (DefaultsScope.runas (← list1 (member userAtom)))
    | some '!' => do advance; ws; pure (DefaultsScope.cmnd (← list1 (member (cmndAtom false))))
    | _ => pure DefaultsScope.global
  ws
  return .defaults scope (← list1 defaultsSetting)

/-! ## Entries -/

/-- Include path: quoted, or up to the next blank (`\ ` escapes a blank). -/
def includePath : P String := do
  ws
  if (← peek) == some '"' then return (← readQuoted)
  let mut acc : List Char := []
  for _ in [0:(← fuel)] do
    match (← get) with
    | [] => break
    | c :: cs =>
      if c.c == '\\' then
        match cs with
        | d :: ds =>
          if d.c == '\n' || isCont cs then break
          set ds
          acc := d.c :: acc
        | [] => break
      else if isBlank c.c || c.c == '\n' then break
      else
        set cs
        acc := c.c :: acc
  if acc.isEmpty then err "missing include path"
  return String.ofList acc.reverse

/-- Skip a comment (current char `#`) up to and including the newline. -/
def skipComment : P Unit := do
  for _ in [0:(← fuel)] do
    match (← get) with
    | [] => break
    | c :: cs =>
      set cs
      if c.c == '\n' then break

/-- End of an entry: blanks, then end of line, end of file or a comment. -/
def endOfEntry : P Unit := do
  ws
  match (← get) with
  | [] => pure ()
  | c :: cs =>
    if c.c == '\n' then set cs
    else if c.c == '#' && !(cs.head?.map (·.c.isDigit)).getD false then skipComment
    else err s!"unexpected {describe (some c.c)}"

/-- Keyword followed by a blank (or a line continuation). -/
def keyword (inp : List PChar) (kw : String) : Option (List PChar) :=
  match stripPrefix inp kw.toList with
  | some (c :: cs) =>
    if isBlank c.c || (c.c == '\\' && isCont cs) then some (c :: cs) else none
  | _ => none

/-- `Defaults` followed by a scope marker, blank, or end of line. -/
def defaultsKeyword (inp : List PChar) : Option (List PChar) :=
  match stripPrefix inp "Defaults".toList with
  | some [] => some []
  | some (c :: cs) =>
    if isBlank c.c || c.c == '\n' || c.c == '@' || c.c == ':' || c.c == '>' || c.c == '!' ||
        (c.c == '\\' && isCont cs) then some (c :: cs)
    else none
  | none => none

/-- Parse one entry starting at the current (non-blank) character. -/
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
    try1 "Cmnd_Alias" do
      return (← aliasDefs (member (cmndAtom true))).map fun (n, ms) => .cmndAlias n ms,
    try1 "Cmd_Alias" do
      return (← aliasDefs (member (cmndAtom true))).map fun (n, ms) => .cmndAlias n ms]
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
          (keyword (c :: cs) "#include").isNone && (keyword (c :: cs) "#includedir").isNone then
        skipComment
        continue
      let es ← entry
      endOfEntry
      acc := (es.reverse.map fun e => { file, line := c.line, entry := e }) ++ acc
  err "input too long"

/-! ## Post-conditions -/

/-- Command atoms occurring anywhere in an entry. -/
def cmndAtoms : Entry → List CmndAtom
  | .cmndAlias _ ms => ms.map (·.atom)
  | .defaults (.cmnd cs) _ => cs.map (·.atom)
  | .userSpec s => s.entries.flatMap fun hc => hc.cmnds.map (·.cmnd.atom)
  | _ => []

/-- `command p _` only with an absolute `p`. -/
def CmndAtom.pathOk : CmndAtom → Bool
  | .command p _ => p.toList.head? == some '/'
  | _ => true

def wellFormed (file : String) (l : Located) : Bool :=
  decide (1 ≤ l.line) && l.file == file && (cmndAtoms l.entry).all CmndAtom.pathOk

/-- Defence in depth: reject (as an internal error) any result violating `wellFormed`. -/
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
/-- Parse the text of one sudoers file. `file` is used for `Located.file` and errors. -/
def parse (file : String) (text : String) : Except ParseError (List Located) :=
  match (entries (context file text)).run (annotate text.toList 1 1 []) with
  | .error e => .error e
  | .ok (es, _) => check file es

/-! ## Theorems -/

theorem parse_wellFormed {file text : String} {es : List Located}
    (h : parse file text = .ok es) : ∀ l ∈ es, Parser.wellFormed file l = true := by
  unfold parse at h
  split at h
  · cases h
  · exact Parser.check_ok h

/-- Every parsed entry records a 1-based line. -/
theorem parse_line_pos {file text : String} {es : List Located}
    (h : parse file text = .ok es) : ∀ l ∈ es, 1 ≤ l.line := by
  intro l hl
  have := parse_wellFormed h l hl
  simp only [Parser.wellFormed, Bool.and_eq_true, decide_eq_true_eq] at this
  exact this.1.1

/-- Every parsed entry records the given file name. -/
theorem parse_file_eq {file text : String} {es : List Located}
    (h : parse file text = .ok es) : ∀ l ∈ es, l.file = file := by
  intro l hl
  have := parse_wellFormed h l hl
  simp only [Parser.wellFormed, Bool.and_eq_true, beq_iff_eq] at this
  exact this.1.2

/-- The parser never yields a command atom with a non-absolute path. -/
theorem parse_command_absolute {file text : String} {es : List Located}
    (h : parse file text = .ok es) :
    ∀ l ∈ es, ∀ p a, CmndAtom.command p a ∈ Parser.cmndAtoms l.entry →
      p.toList.head? = some '/' := by
  intro l hl p a hm
  have := parse_wellFormed h l hl
  simp only [Parser.wellFormed, Bool.and_eq_true, List.all_eq_true] at this
  have := this.2 _ hm
  simpa [Parser.CmndAtom.pathOk] using this

end LeanSudo.Sudoers
