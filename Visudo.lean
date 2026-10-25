import LeanSudo.Visudo.Core
import LeanSudo.Visudo.Sys
import LeanSudo.Sudoers.Load
import LeanSudo.Sys.Core
import LeanSudo.Sys.Extra
import LeanSudo.I18n.Load

/-!
# `visudo` entry point

* **Check mode** (`-c`): parse the sudoers file and everything it includes, run the
  semantic checks of `LeanSudo.Visudo.Core`, and print `<file>: parsed OK` per file.
  Without `-f` (or with `-O`/`-P`) every file must also be owned by 0:0 / have mode
  0440, as in sudo.ws. `-f -` reads standard input.
* **Edit mode**: lock the original files with record locks compatible with sudo.ws,
  reuse their `.tmp` copies, and edit the main file and explicit includes in order.
  All changes are checked together before installation; `-I` suppresses editing
  includes, not parsing them. `What now?` supports re-edit, discard and force-save.
* **Export**: the upstream compatibility invocation of `cvtsudoers` via PATH.
-/

open LeanSudo LeanSudo.Sys LeanSudo.Sudoers LeanSudo.Policy LeanSudo.Visudo

namespace VisudoMain

/-! ## Loading a policy file by file -/

structure LoadState where
  /-- every file read, in order (main file first) -/
  files : Array String := #[]
  entries : Array Located := #[]
  errors : Array String := #[]
  warnings : Array String := #[]
  strict : Bool := false
  editable : Array String := #[]
  sources : List (String × String) := []
  overrides : List (String × String) := []
  createMode : Option UInt32 := none

abbrev LoadM := StateT LoadState IO

def addError (e : String) : LoadM Unit := modify fun s => { s with errors := s.errors.push e }
def addWarning (w : String) : LoadM Unit := modify fun s => { s with warnings := s.warnings.push w }

def lockOrFail (path : String) (mode : UInt32) : IO Unit := do
  if (← lockFile path mode) == .busy then
    throw (IO.userError s!"{path} busy, try again later")

def readSudoers (path : String) : IO (Except String String) := do
  match ← (readFileFollow path).toBaseIO with
  | .ok (_, text) => pure (.ok text)
  | .error e => pure (.error (toString e))

/-- Only visudo -s validates path ERE tokens. Upstream's GOTREGEX action
checks the final `$` token rather than the accumulated argument expression, so
argument ERE validity remains a runtime check even in strict mode. -/
def commandRegexes : CmndAtom → List String
  | .commandRegex re _ => [re]
  | .digest _ c => commandRegexes c
  | _ => []

def checkRegexes (loc : Located) (text : String) : LoadM Unit := do
  for re in (Sudoers.Parser.cmndAtoms loc.entry).flatMap commandRegexes do
    try
      let _ ← Sys.regexMatches re ""
    catch e =>
      let lines := text.splitOn "\n"
      let mut line := loc.line
      let mut col := 1
      for (ln, index) in (lines.drop (loc.line - 1)).zipIdx do
        match ln.splitOn re with
        | beforeToken :: _ :: _ =>
          line := loc.line + index
          col := beforeToken.length + 1
          break
        | _ => pure ()
      let ln := lines[line - 1]?.getD ""
      let pad := String.ofList ((ln.toList.take (col - 1)).map fun c =>
        if c == '\t' then '\t' else ' ')
      let underline := String.ofList (List.replicate (re.length - 1) '~')
      addError s!"{loc.file}:{line}:{col}: {e}\n{ln}\n{pad}^{underline}"

mutual
partial def loadText (host : String) (depth : Nat) (path text : String) : LoadM Unit := do
  modify fun s => { s with
    files := if s.files.contains path then s.files else s.files.push path
    sources := (path, text) :: s.sources }
  match parse path text with
  | .error e => addError (renderSyntaxError e text)
  | .ok es =>
    for l in es do
      for warning in l.warnings do addWarning warning
      if (← get).strict then checkRegexes l text
      match l.entry with
      | .include raw =>
        let target := resolveIncludePath path host raw
        unless (← get).files.contains target do
          modify fun s => { s with editable := s.editable.push target }
        includeFile host (depth + 1) target
      | .includeDir raw => includeDir host (depth + 1) (resolveIncludePath path host raw)
      | _ => modify fun s => { s with entries := s.entries.push l }

partial def includeFile (host : String) (depth : Nat) (path : String) : LoadM Unit := do
  if depth > maxDepth then
    addError s!"{path}: too many levels of includes"
  else
    if let some mode := (← get).createMode then
      lockOrFail path mode
    let source := ((← get).overrides.lookup path).getD path
    match ← readSudoers source with
    | .ok text => loadText host depth path text
    | .error e =>
      let e := if e.startsWith "unable to open " then (e.drop 15).toString else e
      addError s!"visudo: {e}"

partial def includeDir (host : String) (depth : Nat) (dir : String) : LoadM Unit := do
  -- A missing directory is ignored; an insecure one is skipped (as sudo does).
  let some st ← stat dir | return
  match checkDirPerms dir st with
  | .error msg => addWarning s!"visudo: {msg}"
  | .ok () =>
    match ← (listDir dir).toBaseIO with
    | .error e => addWarning s!"visudo: {dir}: {e}"
    | .ok names =>
      for name in (names.filter includeDirEntryOk).mergeSort (· < ·) do
        let path := dir ++ "/" ++ name
        let some st ← stat path | continue
        if !st.isReg then continue
        if let some mode := (← get).createMode then
          lockOrFail path mode
        if depth > maxDepth then
          addError s!"{path}: too many levels of includes"
        else
          let source := ((← get).overrides.lookup path).getD path
          match ← readSudoers source with
          | .ok text => loadText host depth path text
          | .error e => addWarning s!"visudo: {e}"
end

/-- Result of checking a complete policy. -/
structure Analysis where
  files : Array String
  entries : List Located
  /-- syntax, include and semantic errors (any ⇒ the policy is rejected) -/
  errors : List String
  warnings : List String
  /-- Parser and applied Defaults warnings, also emitted before the first editor. -/
  initialWarnings : List String
  settings : Settings
  editable : Array String

def sourceLine (sources : List (String × String)) (loc : Located) : String :=
  (((sources.lookup loc.file).getD "").splitOn "\n")[loc.line - 1]?.getD ""

def aliasColumn (line : String) : Nat :=
  let chars := line.toList
  let rest := ((chars.dropWhile Char.isWhitespace).dropWhile (!·.isWhitespace)).dropWhile Char.isWhitespace
  chars.length - rest.length + 1

/-- The shared AST stores entry lines; recover upstream's diagnostic columns from
the retained source, without altering the runtime policy representation. -/
def semanticDiagnostic (sources : List (String × String)) (entries : List Located)
    (message : String) : String := Id.run do
  let warning := message.startsWith "Warning: "
  let body := if warning then (message.drop 9).toString else message
  let some loc := entries.find? (fun l => body.startsWith (locPos l ++ ": ")) | return message
  let line := sourceLine sources loc
  let detail := (body.drop (locPos loc).length).toString
  let column := match loc.entry with
    | .userSpec _ => line.length + 1
    | .defaults _ settings =>
      let relevant := settings.find? fun d => detail.contains d.name
      match relevant with
      | none => line.length + 1
      | some d =>
        let before := (line.splitOn d.name).head!
        before.length + d.name.length + 1 +
          (match d.op with | .assign _ => 1 | .add _ | .remove _ => 2 | _ => 0)
    | _ => if detail.startsWith ": duplicate " then line.length + 1 else aliasColumn line
  let mut rendered := (if warning then "Warning: " else "") ++
    s!"{locPos loc}:{column}{detail}"
  if detail.startsWith ": duplicate " then
    for previous in entries do
      let marker := "previously defined at " ++ locPos previous
      if rendered.endsWith marker then
        rendered := rendered ++ s!":{aliasColumn (sourceLine sources previous)}"
        break
    rendered := rendered ++ "\n" ++ line ++ "\n" ++
      String.ofList (List.replicate (column - 1) ' ') ++ "^"
  return rendered

def invokingPrincipal : IO (Option Principal) := do
  let uid ← getuid
  let name ← if (← geteuid) == 0 then IO.getEnv "SUDO_USER" else pure none
  let named ← match name.filter (!·.isEmpty) with
    | some name => getpwnam name
    | none => pure none
  let some pw ← if named.isSome then pure named else getpwuid uid | return none
  let gids ← getgrouplist pw.name pw.gid
  let groups ← gids.filterMapM fun g => do
    return (← getgrgid g).map fun gi => (gi.name, gi.gid)
  return some { name := pw.name, uid := pw.uid, gid := pw.gid, groups,
                home := pw.home, shell := pw.shell }

def analyze (host path text : String) (strict : Bool)
    (overrides : List (String × String) := []) (createMode : Option UInt32 := none) :
    IO Analysis := do
  let ((), s) ← (loadText host 0 path text).run { strict, overrides, createMode }
  let entries := s.entries.toList
  let sem := if s.errors.isEmpty then semanticErrors entries strict else []
  let warnings := if s.errors.isEmpty then semanticWarnings entries strict else []
  let user ← if s.errors.isEmpty then invokingPrincipal else pure none
  let applied : Settings × List String := (user.bind fun user =>
    (resolveDefaults (entries.map (·.entry)) user host none none (verbose := true)).toOption).getD ({}, [])
  -- Unknown Defaults warnings are already fatal, source-located type errors.
  -- Keep callback warnings here without duplicating those semantic diagnostics.
  let callbacks := applied.2.filter fun warning => !sem.any (·.endsWith warning)
  pure { files := s.files, entries,
         errors := s.errors.toList ++ sem.map (semanticDiagnostic s.sources entries),
         warnings := warnings.map (semanticDiagnostic s.sources entries),
         initialWarnings := s.warnings.toList ++ callbacks, settings := applied.1,
         editable := s.editable }

def shortHost : IO String := do
  match (← gethostname).splitOn "." with
  | h :: _ => pure h
  | [] => pure ""

def eprint (s : String) : IO Unit := do IO.eprintln (← I18n.translate s)

/-! ## Check mode -/

def readStdin : IO String := do
  let stdin ← IO.getStdin
  let mut acc := ""
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    acc := acc ++ line
  pure acc

/-- sudo.ws's `check_file`: owner 0:0 and mode exactly 0440 (when enforced). -/
def ownerPermProblems (path : String) (owner perms : Bool) : IO (List String) := do
  let some st ← stat path | return []
  let o := if owner && (st.uid != 0 || st.gid != 0) then
      [s!"{path}: wrong owner (uid, gid) should be (0, 0)"] else []
  let p := if perms && (st.mode &&& 0o7777) != 0o440 then
      [s!"{path}: bad permissions, should be mode 0440"] else []
  pure (o ++ p)

def checkMode (o : Options) (path : String) : IO UInt32 := do
  let say (s : String) : IO Unit := unless o.quiet do eprint s
  let (name, text) ← if path == "-" then pure ("stdin", ← readStdin) else
    match ← readSudoers path with
    | .ok t => pure (path, t)
    | .error e => say s!"visudo: {e}"; return 1
  let a ← analyze (← shortHost) name text o.strict
  a.initialWarnings.forM say
  for error in a.errors do
    if error.startsWith "visudo: " then eprint error else say error
  a.warnings.forM say
  unless a.errors.isEmpty do return 1
  let enforceOwner := o.owner || o.file.isNone
  let enforcePerms := o.perms || o.file.isNone
  let mut ok := true
  for f in a.files do
    let probs ← if name == "stdin" && f == name then pure []
      else ownerPermProblems f enforceOwner enforcePerms
    if probs.isEmpty then
      unless o.quiet do IO.println (← I18n.translate s!"{f}: parsed OK")
    else
      ok := false
      probs.forM say
  pure (if ok then 0 else 1)

/-! ## Edit mode -/

def isExecFile (p : String) : IO Bool := do
  match ← stat p with
  | some st => if st.isReg then access p 1 else pure false
  | none => pure false

/-- `p` made absolute against the current directory. -/
def absolutize (p : String) : IO String := do
  if p.startsWith "/" then pure p else pure ((← getcwd) ++ "/" ++ p)

/-- Absolute path of an editor command (PATH lookup when it has no `/`). -/
def resolveCmd (env : List (String × String)) (cmd : String) : IO (Option String) := do
  if cmd.isEmpty then return none
  if cmd.contains '/' then
    if ← isExecFile cmd then return some (← absolutize cmd)
    return none
  for d in ((env.lookup "PATH").getD "/usr/bin:/bin").splitOn ":" do
    let p := (if d.isEmpty then "." else d) ++ "/" ++ cmd
    if ← isExecFile p then return some (← absolutize p)
  return none

/-- sudo's editor choice: `(path, argv0, extra args)` or the error message. -/
def chooseEditor (st : Settings) (env : List (String × String)) :
    IO (Except String (String × String × List String)) := do
  let list := (st.editor.splitOn ":").filter (!·.isEmpty)
  let envVals := envEditorValues env
  if st.envEditor && !envVals.isEmpty then
    let mut last := ""
    for v in envVals do
      last := v
      match splitWords v with
      | cmd :: args =>
        if let some p ← resolveCmd env cmd then return .ok (p, cmd, args)
      | [] => pure ()
    return .error s!"specified editor ({last}) doesn't exist"
  if !st.envEditor then
    -- the user's editor is only allowed if it is one of the `editor` list
    for v in envVals do
      match splitWords v with
      | cmd :: args =>
        if let some p ← resolveCmd env cmd then
          if list.any (fun e => e == p || e == cmd) then return .ok (p, cmd, args)
      | [] => pure ()
  for e in list do
    match splitWords e with
    | cmd :: args =>
      if let some p ← resolveCmd env cmd then return .ok (p, cmd, args)
    | [] => pure ()
  return .error s!"no editor found (editor path = {st.editor})"


partial def whatNow : IO Char := do
  let out ← IO.getStdout
  out.putStr (← I18n.gettext "What now? ")
  out.flush
  let line ← (← IO.getStdin).getLine
  if line.isEmpty then return 'x'
  match whatNowChoice line with
  | some c => return c
  | none =>
    out.putStr (← I18n.translate whatNowHelp)
    whatNow

def removeQuietly (p : String) : IO Unit :=
  try IO.FS.removeFile p catch _ => pure ()

/-- A session retains all originals and temporary copies until the entire policy
has been checked, so an error in an include can never partially install an edit. -/
structure EditFile where
  path : String
  original : FileStat
  created : Bool
  modified : Bool := false
  deriving Inhabited

def EditFile.tmp (f : EditFile) : String := f.path ++ ".tmp"

def openEditFile (path : String) (mode : UInt32) : IO EditFile := do
  let created := (← stat path).isNone
  lockOrFail path mode
  let (st, text) ← readFileFollow path
  createTemp (path ++ ".tmp") (withFinalNewline text)
  copyFileTime path (path ++ ".tmp")
  pure { path, original := st, created }

def supportsLineNumber (editor : String) : Bool :=
  let base := (editor.splitOn "/").getLast!
  let base := if base.startsWith "r" then (base.drop 1).toString else base
  base.endsWith "macs" ||
    ["ee", "elvis", "ex", "joe", "jove", "mg", "nano", "nex", "nvi", "nvim",
     "o", "pico", "vi", "vile", "vim", "zile"].contains base

def editFile (f : EditFile) (mainFile : Bool)
    (editor : String × String × List String) (line : Nat := 0) : IO EditFile := do
  let (edPath, argv0, edArgs) := editor
  let args := #[argv0] ++ edArgs.toArray ++
    (if line > 0 && supportsLineNumber edPath then #[s!"+{line}"] else #[]) ++ #["--", f.tmp]
  unless ← runEditor edPath args do
    eprint s!"visudo: editor ({edPath}) failed, {f.path} unchanged"
    return f
  let some st ← stat f.tmp | do
    eprint s!"visudo: unable to stat temporary file ({f.tmp}), {f.path} unchanged"
    return f
  if mainFile && st.size == 0 && f.original.size != 0 then
    eprint s!"visudo: zero length temporary file ({f.tmp}), {f.path} unchanged"
    return f
  let modified ← fileModified f.path f.tmp
  unless modified do
    eprint s!"visudo: {f.tmp} unchanged"
  return { f with modified := f.modified || modified }

def promptInclude (path : String) : IO Unit := do
  let out ← IO.getStdout
  out.putStr (← I18n.translate s!"press return to edit {path}: ")
  out.flush
  let _ ← (← IO.getStdin).getLine

def editInclude (files : IO.Ref (Array EditFile)) (path : String) (mode : UInt32)
    (editor : String × String × List String) : IO EditFile := do
  promptInclude path
  let f ← openEditFile path mode
  files.modify (·.push f)
  let f ← editFile f false editor
  files.modify fun fs => fs.set! (fs.size - 1) f
  return f

def installFile (o : Options) (f : EditFile) (mainFile : Bool) : IO Unit := do
  let useOwner := o.owner || o.file.isNone
  let usePerms := o.perms || o.file.isNone
  let uid := if useOwner then 0 else f.original.uid
  let gid := if useOwner then 0 else f.original.gid
  let mode := if usePerms then 0o440 else f.original.mode &&& 0o777
  if f.modified then
    setOwnerMode f.tmp uid gid mode
    IO.FS.rename f.tmp f.path
  else
    removeQuietly f.tmp
    if mainFile && f.created then removeQuietly f.path
    else if useOwner || usePerms then
      correctLockedMetadata f.path uid.toUInt32 gid.toUInt32 mode.toUInt32 useOwner usePerms

partial def checkEdits (o : Options) (host : String) (session : IO.Ref (Array EditFile))
    (known : IO.Ref (Array String)) (editor : String × String × List String)
    (mode : UInt32) :
    IO (Option (Array EditFile)) := do
  let files ← session.get
  let mainFile := files[0]!
  let text ← match ← readSudoers mainFile.tmp with
    | .ok text => pure text
    | .error _ => throw (IO.userError
        s!"unable to re-open temporary file ({mainFile.tmp}), {mainFile.path} unchanged.")
  let overrides := files.toList.map fun f => (f.path, f.tmp)
  let a ← analyze host mainFile.path text o.strict overrides (some mode)
  unless o.quiet do
    a.initialWarnings.forM eprint
    a.errors.forM eprint
    a.warnings.forM eprint
  let mut files := files
  let mut reparse := false
  unless a.errors.isEmpty do
    match ← whatNow with
    | 'x' => return none
    | 'Q' => pure ()
    | _ =>
      for path in a.files do
        let error := a.errors.find? (fun e => e.startsWith (path ++ ":"))
        if let some error := error then
          unless files.any (·.path == path) do
            files := files.push (← openEditFile path mode)
            session.set files
          let line := (((error.drop (path.length + 1)).toString.splitOn ":").head!).toNat?.getD 0
          for i in [:files.size] do
            let f := files[i]!
            if f.path == path then
              files := files.set! i (← editFile f (i == 0) editor line)
              session.set files
      reparse := true
  -- Upstream opens every file discovered during reparsing, even under -I:
  -- that option suppresses the initial include-edit pass only.
  let previous ← known.get
  known.set (previous ++ a.files.filter (!previous.contains ·))
  for path in a.files do
    unless previous.contains path || files.any (·.path == path) do
      let f ← editInclude session path mode editor
      files ← session.get
      reparse := reparse || f.modified
  if reparse then checkEdits o host session known editor mode else pure (some files)

def editMode (o : Options) (path : String) : IO UInt32 := do
  let mode : UInt32 := if o.file.isSome && !o.perms then 0o640 else 0o440
  let files ← IO.mkRef (#[] : Array EditFile)
  try
    let created := (← stat path).isNone
    lockOrFail path mode
    let (_, text) ← readFileFollow path
    let host ← shortHost
    let current ← analyze host path text o.strict [] (some mode)
    unless o.quiet do
      current.initialWarnings.forM eprint
      current.errors.forM eprint
    let editor ← match ← chooseEditor current.settings (← environ) with
      | .ok ed => pure ed
      | .error e => throw (IO.userError e)
    let first ← openEditFile path mode
    let first := { first with created }
    files.set #[first]
    files.set #[(← editFile first true editor)]
    unless o.noIncludes do
      for includePath in current.editable do
        let _ ← editInclude files includePath mode editor
    let known ← IO.mkRef current.files
    let mut exitCode : UInt32 := 0
    let mut retained : Array String := #[]
    match ← checkEdits o host files known editor mode with
    | none => pure ()
    | some checked =>
      files.set checked
      for i in [:checked.size] do
        let f := checked[i]!
        try
          installFile o f (i == 0)
        catch e =>
          exitCode := 1
          eprint s!"visudo: {e}"
          if (← stat f.tmp).isSome then
            eprint s!"visudo: contents of edit session left in {f.tmp}"
            retained := retained.push f.tmp
    for f in ← files.get do
      unless retained.contains f.tmp do removeQuietly f.tmp
    return exitCode
  catch e =>
    eprint s!"visudo: {e}"
    for f in ← files.get do removeQuietly f.tmp
    return 1

end VisudoMain

def main (args : List String) : IO UInt32 := do
  I18n.initializeLocale
  match parseArgs args with
  | .error e =>
    unless e.isEmpty do VisudoMain.eprint s!"visudo: {e}"
    VisudoMain.eprint usageLine
    return 1
  | .ok o =>
    if o.help then
      IO.print (← I18n.translate helpText)
      return 0
    if o.version then
      IO.print (← I18n.translate versionText)
      return 0
    let path := o.file.getD mainSudoersPath
    if let some output := o.exportFile then
      VisudoMain.eprint "visudo: the -x option will be removed in a future release"
      VisudoMain.eprint "visudo: please consider using the cvtsudoers utility instead"
      try
        exportSudoers path output
      catch e =>
        VisudoMain.eprint s!"visudo: {e}"
      return 1
    if o.check then VisudoMain.checkMode o path else VisudoMain.editMode o path
