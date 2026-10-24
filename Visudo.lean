import LeanSudo.Visudo.Core
import LeanSudo.Visudo.Sys
import LeanSudo.Sudoers.Load
import LeanSudo.Sys.Core
import LeanSudo.Sys.Exec

/-!
# `visudo` entry point

* **Check mode** (`-c`): parse the sudoers file and everything it includes, run the
  semantic checks of `LeanSudo.Visudo.Core`, and print `<file>: parsed OK` per file.
  Without `-f` (or with `-O`/`-P`) every file must also be owned by 0:0 / have mode
  0440, as in sudo.ws. `-f -` reads standard input.
* **Edit mode** (root only): lock the file (`F_OFD_SETLK`, compatible with sudo.ws's
  lock) and create `<file>.tmp` with `O_EXCL` (an existing temp file means another
  edit is in progress, or a crashed one left it behind: `<file> busy, try again
  later`). The editor (`SUDO_EDITOR`/`VISUAL`/`EDITOR` under `env_editor`, else the
  `editor` list) runs as root on the temp file. The result is re-checked like `-c`;
  on errors `What now?` offers `e` (edit again), `x` (discard) and `Q` (install
  anyway). A valid result is chowned/chmodded (0:0 0440, or the original owner/mode
  with `-f` and no `-O`/`-P`) and renamed over the original.

Only the main file (or the `-f` file) is ever edited; included files are checked but
not opened in the editor (so `-I` changes nothing). Include-directory entries that
cannot be read are skipped with a warning (as sudo.ws does); explicit `@include`
targets must be readable.
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

abbrev LoadM := StateT LoadState IO

def addError (e : String) : LoadM Unit := modify fun s => { s with errors := s.errors.push e }
def addWarning (w : String) : LoadM Unit := modify fun s => { s with warnings := s.warnings.push w }

def readSudoers (path : String) : IO (Except String String) := do
  match ← (readFileNoFollow path).toBaseIO with
  | .ok (_, text) => pure (.ok text)
  | .error e => pure (.error (toString e))

mutual
partial def loadText (host : String) (depth : Nat) (path text : String) : LoadM Unit := do
  modify fun s => { s with files := s.files.push path }
  match parse path text with
  | .error e => addError (renderSyntaxError e text)
  | .ok es =>
    for l in es do
      match l.entry with
      | .include raw => includeFile host (depth + 1) (resolveIncludePath path host raw)
      | .includeDir raw => includeDir host (depth + 1) (resolveIncludePath path host raw)
      | _ => modify fun s => { s with entries := s.entries.push l }

partial def includeFile (host : String) (depth : Nat) (path : String) : LoadM Unit := do
  if depth > maxDepth then
    addError s!"{path}: too many levels of includes"
  else
    match ← readSudoers path with
    | .ok text => loadText host depth path text
    | .error e => addError s!"visudo: {e}"

partial def includeDir (host : String) (depth : Nat) (dir : String) : LoadM Unit := do
  -- A missing directory is ignored; an insecure one is skipped (as sudo does).
  let some st ← lstat dir | return
  match checkDirPerms dir st with
  | .error msg => addWarning s!"visudo: {msg}"
  | .ok () =>
    match ← (listDir dir).toBaseIO with
    | .error e => addWarning s!"visudo: {dir}: {e}"
    | .ok names =>
      for name in sortNames (names.filter includeDirEntryOk) do
        let path := dir ++ "/" ++ name
        if depth > maxDepth then
          addError s!"{path}: too many levels of includes"
        else
          match ← readSudoers path with
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

def analyze (host path text : String) : IO Analysis := do
  let ((), s) ← (loadText host 0 path text).run {}
  let entries := s.entries.toList
  let sem := if s.errors.isEmpty then semanticErrors entries else []
  let unused := if s.errors.isEmpty && sem.isEmpty then semanticWarnings entries else []
  pure { files := s.files, entries, errors := s.errors.toList ++ sem,
         warnings := s.warnings.toList ++ unused }

def shortHost : IO String := do
  match (← gethostname).splitOn "." with
  | h :: _ => pure h
  | [] => pure ""

def eprint (s : String) : IO Unit := IO.eprintln s

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
  let a ← analyze (← shortHost) name text
  a.warnings.forM say
  unless a.errors.isEmpty do
    a.errors.forM say
    return 1
  let enforceOwner := o.owner || o.file.isNone
  let enforcePerms := o.perms || o.file.isNone
  let mut ok := true
  for f in a.files do
    let probs ← if name == "stdin" && f == name then pure []
      else ownerPermProblems f enforceOwner enforcePerms
    if probs.isEmpty then
      unless o.quiet do IO.println s!"{f}: parsed OK"
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

def invokingPrincipal : IO (Option Principal) := do
  let uid ← getuid
  let some pw ← getpwuid uid | return none
  let gids ← getgrouplist pw.name pw.gid
  let groups ← gids.filterMapM fun g => do
    return (← getgrgid g).map fun gi => (gi.name, gi.gid)
  return some { name := pw.name, uid, gid := pw.gid, groups, home := pw.home, shell := pw.shell }

/-- Settings for the editor choice: the current policy's global/host/user `Defaults`,
or the compiled-in defaults if it does not load. -/
def editorSettings (host : String) (a : Analysis) : IO Settings := do
  unless a.errors.isEmpty do return {}
  let some user ← invokingPrincipal | return {}
  match resolveDefaults (a.entries.map (·.entry)) user host none none with
  | .ok (st, _) => pure st
  | .error _ => pure {}

partial def whatNow : IO Char := do
  let out ← IO.getStdout
  out.putStr "What now? "
  out.flush
  let line ← (← IO.getStdin).getLine
  if line.isEmpty then return 'x'
  match whatNowChoice line with
  | some c => return c
  | none =>
    out.putStr whatNowHelp
    whatNow

def removeQuietly (p : String) : IO Unit :=
  try IO.FS.removeFile p catch _ => pure ()

/-- Editor loop on the existing temp file; returns the exit status. -/
partial def editLoop (o : Options) (host path tmp initial : String) (orig : Option FileStat)
    (editor : String × String × List String) (umask : Nat) : IO UInt32 := do
  let (edPath, argv0, edArgs) := editor
  let env ← environ
  let spec : ExecSpec := {
    path := edPath
    argv := #[argv0] ++ edArgs.toArray ++ #["--", tmp]
    env := (env.map fun (k, v) => k ++ "=" ++ v).toArray
    uid := ← geteuid, gid := ← getegid, groups := (← getgroups).toArray
    cwd := none, umask, usePty := false, background := false }
  match ← (runCommand spec).toBaseIO with
  | .error e =>
    eprint s!"visudo: {e}"
    eprint s!"visudo: editor ({edPath}) failed, {path} unchanged"
    removeQuietly tmp
    return 1
  | .ok _ => pure ()  -- like sudo.ws, the editor's exit status is not significant
  let text ← match ← readSudoers tmp with
    | .ok t => pure t
    | .error e => eprint s!"visudo: {e}"; removeQuietly tmp; return 1
  if text.isEmpty then
    eprint s!"visudo: zero length temporary file ({tmp}), {path} unchanged"
    removeQuietly tmp
    return 0
  if orig.isSome && text == initial then
    unless o.quiet do eprint s!"visudo: {tmp} unchanged"
    removeQuietly tmp
    return 0
  let a ← analyze host path text
  unless o.quiet do a.warnings.forM eprint
  unless a.errors.isEmpty do
    a.errors.forM eprint
    match ← whatNow with
    | 'e' => return ← editLoop o host path tmp initial orig editor umask
    | 'Q' => pure ()
    | _ => removeQuietly tmp; return 0
  -- install: owner/mode, then atomically replace the original
  let useOwner := o.owner || o.file.isNone || orig.isNone
  let usePerms := o.perms || o.file.isNone || orig.isNone
  let (uid, gid) := match orig with
    | some st => if useOwner then (0, 0) else (st.uid, st.gid)
    | none => (0, 0)
  let mode := match orig with
    | some st => if usePerms then 0o440 else st.mode &&& 0o7777
    | none => 0o440
  try
    setOwnerMode tmp uid gid mode
    IO.FS.rename tmp path
    return 0
  catch e =>
    eprint s!"visudo: unable to install {path}: {e}"
    removeQuietly tmp
    return 1

def editMode (o : Options) (path : String) : IO UInt32 := do
  if path == "-" then
    eprint "visudo: standard input can only be checked (-c)"
    return 1
  if (← geteuid) != 0 then
    eprint s!"visudo: you must be root to edit {path}"
    return 1
  let oldUmask ← umask 0o077
  match ← (lockFile path).toBaseIO with
  | .error e => eprint s!"visudo: {e}"; return 1
  | .ok .busy => eprint s!"visudo: {path} busy, try again later"; return 1
  | .ok _ => pure ()
  let (orig, text) ← match ← (readFileNoFollow path).toBaseIO with
    | .ok (st, t) => pure (some st, t)
    | .error e =>
      if (← lstat path).isSome then
        eprint s!"visudo: {e}"
        return 1
      pure (none, "")
  let host ← shortHost
  let current ← analyze host path text
  unless o.quiet do
    current.warnings.forM eprint
    current.errors.forM eprint
  let editor ← match ← chooseEditor (← editorSettings host current) (← environ) with
    | .ok ed => pure ed
    | .error e => eprint s!"visudo: {e}"; return 1
  let initial := withFinalNewline text
  let tmp := path ++ ".tmp"
  match ← (createExcl tmp initial).toBaseIO with
  | .error e => eprint s!"visudo: {e}"; return 1
  | .ok false => eprint s!"visudo: {path} busy, try again later"; return 1
  | .ok true => pure ()
  try
    editLoop o host path tmp initial orig editor oldUmask.toNat
  catch e =>
    eprint s!"visudo: {e}"
    removeQuietly tmp
    return 1

end VisudoMain

def main (args : List String) : IO UInt32 := do
  match parseArgs args with
  | .error e =>
    unless e.isEmpty do IO.eprintln s!"visudo: {e}"
    IO.eprintln usageLine
    return 1
  | .ok o =>
    if o.help then
      IO.print helpText
      return 0
    if o.version then
      IO.print versionText
      return 0
    let path := o.file.getD mainSudoersPath
    if o.check then VisudoMain.checkMode o path else VisudoMain.editMode o path
