import LeanSudo.Core.Types
import LeanSudo.Sys.Core
import LeanSudo.Sys.Edit
import LeanSudo.Sys.Extra
import LeanSudo.Policy.Eval
import LeanSudo.Sudoedit.Check
import LeanSudo.I18n.Load

def LeanSudo.Core.RunPlan.toSpec (plan : LeanSudo.Core.RunPlan) (path : String)
    (argv env : Array String) (uid gid : Nat) (groups : List Nat) : LeanSudo.Sys.ExecSpec := {
  path, argv, env, uid, gid, groups := groups.toArray,
  cwd := plan.cwd, cwdOptional := plan.cwdOptional, chroot := plan.chroot,
  umask := plan.umask, usePty := plan.usePty, timeout := plan.timeout,
  rlimits := plan.rlimits.toArray, utmpUser := plan.utmpUser, closeFrom := plan.closeFrom,
  execBackground := plan.execBackground, noexecFile := plan.noexecFile,
  apparmorProfile := plan.apparmorProfile, background := false }

namespace LeanSudo.Sudoedit

private def warn (progname s : String) : IO Unit := do
  Sys.writeStderr (progname ++ ": " ++ (← I18n.translate s false) ++ "\n")

private def fileError (path : String) (e : IO.Error) : IO.Error :=
  let text := e.toString
  IO.userError <| if text == "Too many levels of symbolic links" then
    s!"{path}: editing symbolic links is not permitted"
  else if text == "Invalid argument" then s!"{path}: not a regular file"
  else s!"{path}: {text}"

private def writableDir (invoker : Sys.Edit.Identity) (fd : UInt32) : IO Bool := do
  let st ← Sys.Edit.stat fd
  return st[1]! == invoker.uid.toNat || (← Sys.Edit.operation invoker 3 fd).value == 1

private def parentDir (invoker target : Sys.Edit.Identity) (checkdir : Bool)
    (dirs : List String) (file : String) : IO UInt32 := do
  let mut fd := (← Sys.Edit.operation target 7 Sys.Edit.noneFd "/").value
  let check := checkdir && invoker.uid != 0
  try
    for dir in dirs do
      let nofollow := check && (← writableDir invoker fd)
      let next := (← Sys.Edit.operation target (if nofollow then 0 else 7) fd dir).value
      Sys.Edit.close fd
      fd := next
    if check && (← writableDir invoker fd) then
      throw (IO.userError s!"{file}: editing files in a writable directory is not permitted")
    return fd
  catch e =>
    Sys.Edit.close fd
    throw e

private def resolveEditor (who : Sys.Edit.Identity) (path : String)
    (words : List String) : IO (Option String) := do
  let some word := words.head? | return none
  unless words.all Sys.Exec.cSafe do return none
  let paths := if word.contains '/' then [word]
    else
      let dirs := path.splitOn ":"
      (dirs.filter (fun dir => dir != "" && dir != ".") |>.map (· ++ "/" ++ word)) ++
        (if dirs.any (fun dir => dir == "" || dir == ".") then ["./" ++ word] else [])
  let self ← Sys.stat "/proc/self/exe"
  for candidate in paths do
    let opened ← try pure (some (← Sys.Edit.operation who 6 Sys.Edit.noneFd candidate).value)
      catch _ => pure none
    if let some fd := opened then
      let st ← try Sys.Edit.stat fd finally Sys.Edit.close fd
      let same := self.any fun s => s.dev == st[7]! && s.ino == st[8]!
      if same || (candidate.splitOn "/").getLast! == "sudoedit" then
        throw (IO.userError "sudoedit may not be used as an editor")
      if candidate.startsWith "/" then return some candidate
      return some ((← Sys.getcwd) ++ "/" ++ candidate)
  return none

private structure Session where
  file : String
  displayFile : String
  name : String
  parent : UInt32
  temp : String
  original : ByteArray
  originalStat : Array Nat
  tempStat : Array Nat

private def removeTemp (who : Sys.Edit.Identity) (path : String) : IO Unit := do
  let _ ← Sys.Edit.operation who 5 Sys.Edit.noneFd path

private def prepare (progname : String) (invoker target : Sys.Edit.Identity) (follow checkdir : Bool)
    (file displayFile : String) : IO (Option Session) := do
  let some (dirs, name) := pathParts file
    | warn progname s!"{displayFile}: unsafe edit path"; return none
  let parent ← try parentDir invoker target checkdir dirs displayFile
    catch e => warn progname e.toString; return none
  let fd ← try pure (← Sys.Edit.operation target (if follow then 8 else 1) parent name).value
    catch e =>
      Sys.Edit.close parent
      warn progname (fileError displayFile e).toString
      return none
  let mut temp := ""
  try
    let (original, originalStat) ← if fd == Sys.Edit.noneFd then pure (ByteArray.empty, #[])
      else try pure (← Sys.Edit.read fd, ← Sys.Edit.stat fd) finally Sys.Edit.close fd
    let suffixLen := if name.contains '.' then (name.splitOn ".").getLast!.utf8ByteSize + 1 else 0
    let template := tempName name
    let made ← try Sys.Edit.operation invoker 4 Sys.Edit.noneFd s!"/var/tmp/{template}" 0o077 suffixLen
      catch _ => Sys.Edit.operation invoker 4 Sys.Edit.noneFd s!"/tmp/{template}" 0o077 suffixLen
    temp := made.name
    let tempStat ← try
        Sys.Edit.write made.value original ByteArray.empty
        try Sys.Edit.setTimes made.value
              (originalStat[4]?.getD 0).toUInt64 (originalStat[5]?.getD 0).toUInt64
        catch e => warn progname s!"{temp}: {e}"
        Sys.Edit.stat made.value
      finally Sys.Edit.close made.value
    return some { file, displayFile, name, parent, temp, original, originalStat, tempStat }
  catch e =>
    Sys.Edit.close parent
    if temp != "" then
      try removeTemp invoker temp catch _ => pure ()
    throw e

private def copyBack (progname : String) (invoker target : Sys.Edit.Identity) (mask : Nat)
    (follow checkdir elapsed : Bool) (s : Session) : IO Bool := do
  try
    let fd ← try pure (← Sys.Edit.operation invoker 1 Sys.Edit.noneFd s.temp).value
      catch e => throw (fileError s.temp e)
    if fd == Sys.Edit.noneFd then throw (IO.userError s!"{s.temp}: No such file or directory")
    let (bytes, checked, changed) ← try
        let st ← Sys.Edit.stat fd
        let checked := tempSafe ((st[0]! &&& Sys.S_IFMT) == 0o100000)
          (st[1]! == invoker.uid.toNat) (st[6]! == 1)
        unless checked do throw (IO.userError s!"{s.temp}: unsafe temporary file")
        let changed := fileChanged s.tempStat st elapsed
        pure ((← if changed then Sys.Edit.read fd else pure ByteArray.empty), checked, changed)
      finally Sys.Edit.close fd
    if writeBack changed checked then
      let some (dirs, _) := pathParts s.file | throw (IO.userError "unsafe edit path")
      let current ← parentDir invoker target checkdir dirs s.displayFile
      try
        let now ← Sys.Edit.stat current
        let pinned ← Sys.Edit.stat s.parent
        unless now[7]! == pinned[7]! && now[8]! == pinned[8]! do
          throw (IO.userError s!"{s.displayFile}: directory changed during editing")
      finally Sys.Edit.close current
      let out ← try pure (← Sys.Edit.operation target (if follow then 9 else 2) s.parent s.name mask).value
        catch e => throw (fileError s.displayFile e)
      try
        let st ← Sys.Edit.stat out
        unless s.originalStat.isEmpty ||
            (st[7]! == s.originalStat[7]! && st[8]! == s.originalStat[8]! &&
             st[3]! == s.originalStat[3]! && st[4]! == s.originalStat[4]! &&
             st[5]! == s.originalStat[5]!) do
          throw (IO.userError s!"{s.displayFile}: file changed during editing")
        Sys.Edit.write out bytes s.original
      finally Sys.Edit.close out
    else
      warn progname s!"{s.displayFile} unchanged"
    removeTemp invoker s.temp
    return true
  catch e =>
    warn progname e.toString
    warn progname s!"contents of edit session left in {s.temp}"
    return false

structure Editor where
  path : String
  words : List String

def select (progname : String) (plan : Core.EditPlan) : IO (Option Editor) := do
  try
    let invoker ← Sys.Edit.identity plan.editUid plan.editGid plan.editGroups
    let mut resolved := []
    for (words, source) in plan.editors.zip plan.editorSources do
      let result ← resolveEditor invoker plan.editorPath words
      if result.isSome && (words.drop 1).contains "--" then
        warn progname s!"ignoring editor: {source}"
        throw (IO.userError "editor arguments may not contain \"--\"")
      resolved := resolved ++ [(words, result)]
      if result.isSome then break
    let some (path, words) := selectEditor resolved
      | throw (IO.userError s!"{plan.editorNotFound}: command not found")
    if let some root := plan.chroot then
      for candidate in [path, Policy.dirOf path] do
        if ← Sys.rootPathEscapes root candidate then
          throw (IO.userError s!"{path}: command resolves outside the chroot directory")
    return some { path, words }
  catch e =>
    warn progname e.toString
    return none

def run (progname : String) (plan : Core.EditPlan) (editor : Editor)
    (env : Array String) : IO Sys.ExitStatus := do
  let mut sessions : Array Session := #[]
  try
    let invoker ← Sys.Edit.identity plan.editUid plan.editGid plan.editGroups
    let target ← Sys.Edit.identity plan.fileUid plan.fileGid plan.fileGroups
    let mut failed := false
    try
      for (file, displayFile) in plan.files.zip plan.policyFiles do
        if let some session ← prepare progname invoker target plan.follow plan.checkdir file displayFile then
          sessions := sessions.push session
    catch e =>
      for s in sessions do
        try removeTemp invoker s.temp catch _ => pure ()
      throw e
    if sessions.isEmpty then return .exited 1
    let started ← Sys.Edit.clock
    let status ← try
        Sys.runCommand (plan.toRunPlan.toSpec editor.path
          (editor.words.toArray ++ sessions.map (·.temp)) env
          plan.editUid plan.editGid plan.editGroups)
      catch e =>
        warn progname e.toString
        pure (.exited 1)
    let elapsed := started != (← Sys.Edit.clock)
    for s in sessions do
      unless ← copyBack progname invoker target plan.umask plan.follow plan.checkdir elapsed s do failed := true
    return if failed then .exited 1 else status
  catch e =>
    warn progname e.toString
    return .exited 1
  finally
    for s in sessions do Sys.Edit.close s.parent

end LeanSudo.Sudoedit
