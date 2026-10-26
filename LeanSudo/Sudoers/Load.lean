import LeanSudo.Sudoers.Parser
import LeanSudo.Sys.Core

namespace LeanSudo.Sudoers

open LeanSudo.Sys

def mainSudoersPath : String := "/etc/sudoers"

def maxDepth : Nat := 144

private def checkOwnership (kind : Bool) (what path : String) (st : FileStat) :
    Except String Unit :=
  if !kind then .error s!"{path} is not {what}"
  else if st.uid != 0 then .error s!"{path} is owned by uid {st.uid}, should be 0"
  else if st.mode &&& 0o002 != 0 then .error s!"{path} is world writable"
  else if st.mode &&& 0o020 != 0 && st.gid != 0 then
    .error s!"{path} is owned by gid {st.gid}, should be 0"
  else .ok ()

def checkPerms (path : String) (st : FileStat) : Except String Unit :=
  checkOwnership st.isReg "a regular file" path st

def searchComponents (path : String) : List String :=
  (path.splitOn ":").filter (!·.isEmpty)

def resolveIncludePath (searchPath : String) (host : String) (raw : String) : String :=
  let host := if (raw.splitOn "%h").length > 1 then host.map fun c => if c == '/' then '_' else c
    else host
  let rec expand : List Char → List Char
    | '%' :: 'h' :: rest => host.toList ++ expand rest
    | c :: rest => c :: expand rest
    | [] => []
  let p := String.ofList (expand raw.toList)
  if p.startsWith "/" then p else
    ":".intercalate ((searchComponents searchPath).map fun component =>
      match (component.splitOn "/").dropLast with
      | [] => p
      | parts => "/".intercalate parts ++ "/" ++ p)

def firstExisting (path : String) (exists? : String → IO Bool) : IO (Option String) := do
  for candidate in searchComponents path do
    if ← exists? candidate then return some candidate
  return none

def includeDirEntryOk (name : String) : Bool :=
  !name.isEmpty && !name.endsWith "~" && !name.contains '.'

def checkDirPerms (path : String) (st : FileStat) : Except String Unit :=
  checkOwnership st.isDir "a directory" path st

private def readChecked (path : String) : IO (Except String String) := do
  try
    let (st, text) ← readFileFollow path
    return (checkPerms path st).map fun () => text
  catch e => return .error e.toString

private def openIncluded (path : String) : IO (String × Except String String) := do
  match ← firstExisting path fun c => return (← stat c).isSome with
  | some file => return (file, ← readChecked file)
  | none =>
    let first := (searchComponents path).headD path
    match ← readChecked first with
    | .error message =>
      let lead := s!"unable to open {first}: "
      if message.startsWith lead then
        return (first, .error s!"unable to open {path}: {(message.drop lead.length).toString}")
      return (first, .error message)
    | .ok text => return (first, .ok text)

abbrev ScanCache := Array (String × String × Gram.Scan)

def scanCached (cache : ScanCache) (path text : String) (aliases : Array Gram.Alias)
    (scanner : String → String → Array Gram.Alias → Gram.Scan :=
      fun p t a => Gram.scan p t a) : Gram.Scan × ScanCache :=
  match cache.find? (fun (p, t, _) => p == path && t == text) with
  | some (_, _, s) => ({ s with aliases }, cache)
  | none =>
    let s := scanner path text aliases
    (s, if s.definesAliases then cache else cache.push (path, text, s))

structure Journal where
  reason : String
  errstr : Option String := none
  raw : Bool := true

def Journal.text (j : Journal) : String := j.reason ++ ((j.errstr.map (": " ++ ·)).getD "")

def warningJournal (message : String) : Journal :=
  match (message.splitOn ": ").reverse with
  | errstr :: rest@(_ :: _) =>
    if message.startsWith "unable to open " then
      { reason := ": ".intercalate rest.reverse, errstr := some errstr, raw := false }
    else { reason := message, raw := false }
  | _ => { reason := message, raw := false }

inductive LoadResult where
  | ok (entries : List Located)
  | unusable (message : String) (journal : List Journal)
  | failed (journal : List Journal) (recovered : List Located)

structure LoadCtx where
  host : String
  progname : String
  aliases : IO.Ref (Array Gram.Alias)
  failed : IO.Ref Bool
  journal : IO.Ref (Array Journal)
  scans : IO.Ref ScanCache
  parses : IO.Ref (Array (String × String × Except ParseError (List Located)))

def LoadCtx.scan (ctx : LoadCtx) (path text : String) : IO Gram.Scan := do
  let (scan, cache) := scanCached (← ctx.scans.get) path text (← ctx.aliases.get)
  ctx.scans.set cache
  ctx.aliases.set scan.aliases
  return scan

def LoadCtx.parse (ctx : LoadCtx) (path text : String) (scan : Thunk Gram.Scan) :
    IO (Except ParseError (List Located)) := do
  if let some (_, _, r) := (← ctx.parses.get).find? (fun (p, t, _) => p == path && t == text) then
    return r
  let r := parseWith path text scan.get
  unless scan.get.definesAliases do ctx.parses.modify (·.push (path, text, r))
  return r

def LoadCtx.note (ctx : LoadCtx) (j : Journal) : IO Unit := ctx.journal.modify (·.push j)

def LoadCtx.fail (ctx : LoadCtx) (message : String) (prefixed : Bool := true) :
    IO (List Located) := do
  unless message.isEmpty do
    writeStderr ((if prefixed then ctx.progname ++ ": " else "") ++ message ++ "\n")
  ctx.failed.set true
  return []

def LoadCtx.siteError (ctx : LoadCtx) (site : Option (String × Nat × Nat)) : IO Unit := do
  if let some (file, line, col) := site then
    ctx.note { reason := s!"{file}:{line}:{col}: syntax error" }

def includeSites (path : String) (scan : Gram.Scan) : Array (Option (String × Nat × Nat)) :=
  scan.events.filterMap fun
    | .include _ _ line col => some (some (path, line, col))
    | _ => none

mutual
partial def loadText (ctx : LoadCtx) (depth : Nat) (path searchPath text : String) :
    IO (List Located) := do
  let scan ← ctx.scan path text
  let resolve := resolveIncludePath searchPath ctx.host
  let sites := includeSites path scan
  if scan.errors.isEmpty then
    match ← ctx.parse path text (Thunk.pure scan) with
    | .error e => return ← ctx.fail e.toString
    | .ok entries =>
      let mut out : Array Located := #[]
      let mut index := 0
      for loc in entries do
        for warning in loc.warnings do writeStderr (warning ++ "\n")
        match loc.entry with
        | .include raw =>
          out := out ++ (← loadInclude ctx (depth + 1) (resolve raw) (sites.getD index none))
          index := index + 1
        | .includeDir raw =>
          out := out ++ (← loadDir ctx (depth + 1) (resolve raw) (sites.getD index none))
          index := index + 1
        | _ => out := out.push loc
      return out.toList
  ctx.failed.set true
  let kept := Parser.blankOutside text scan.spans
  let recovered ← ctx.parse path kept (Thunk.mk fun _ => Gram.scan path kept)
  let mut pending := (recovered.toOption.getD []).filter
    fun l => match l.entry with | .include _ | .includeDir _ => false | _ => true
  let mut out : Array Located := #[]
  for event in scan.events do
    match event with
    | .warning _ message => writeStderr (message ++ "\n")
    | .include dir raw line col =>
      out := out ++ (pending.filter (·.line < line)).toArray
      pending := pending.filter (·.line ≥ line)
      let site := some (path, line, col)
      out := out ++ (← if dir then loadDir ctx (depth + 1) (resolve raw) site
        else loadInclude ctx (depth + 1) (resolve raw) site)
    | .error e =>
      ctx.note { reason := e.toString }
      discard <| ctx.fail (e.rendered.getD e.toString) false
  return (out ++ pending.toArray).toList

partial def loadInclude (ctx : LoadCtx) (depth : Nat) (path : String)
    (site : Option (String × Nat × Nat)) : IO (List Located) := do
  if depth > maxDepth then
    ctx.siteError site
    return ← ctx.fail s!"{path}: too many levels of includes" false
  match ← openIncluded path with
  | (_, .error message) =>
    ctx.note (warningJournal message)
    ctx.siteError site
    ctx.fail message
  | (file, .ok text) => loadText ctx depth file path text

partial def loadFile (ctx : LoadCtx) (depth : Nat) (path : String) : IO (List Located) := do
  match ← readChecked path with
  | .error message =>
    ctx.note (warningJournal message)
    ctx.fail message
  | .ok text => loadText ctx depth path path text

partial def loadDir (ctx : LoadCtx) (depth : Nat) (path : String)
    (site : Option (String × Nat × Nat)) : IO (List Located) := do
  if depth > maxDepth then
    ctx.siteError site
    return ← ctx.fail s!"{path}: too many levels of includes" false
  let some dir ← firstExisting path fun c => return (← stat c).isSome | return []
  let some st ← stat dir | return []
  if let .error msg := checkDirPerms path st then return ← ctx.fail msg
  let names ← listDir dir
  let mut out : Array Located := #[]
  for name in (names.filter includeDirEntryOk).mergeSort (· < ·) do
    let file := dir ++ "/" ++ name
    let some st ← stat file | continue
    if st.isReg then out := out ++ (← loadFile ctx depth file)
  return out.toList
end

def load (host : String) (path : String := mainSudoersPath) (progname : String := "sudo") :
    IO LoadResult := do
  match ← readChecked path with
  | .error message => return .unusable message [warningJournal message]
  | .ok text =>
    let ctx : LoadCtx := {
      host, progname, aliases := ← IO.mkRef #[], failed := ← IO.mkRef false
      journal := ← IO.mkRef #[], scans := ← IO.mkRef #[], parses := ← IO.mkRef #[] }
    let entries ← loadText ctx 0 path path text
    if ← ctx.failed.get then return .failed (← ctx.journal.get).toList entries
    return .ok entries

end LeanSudo.Sudoers
