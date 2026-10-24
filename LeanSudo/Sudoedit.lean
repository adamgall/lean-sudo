import LeanSudo.Core.Types
import LeanSudo.Sys.Core
import LeanSudo.Sys.Edit
import LeanSudo.Sudoedit.Check

/-!
# sudoedit (`sudo -e`)

Editor selection and copyback gates are pure and proved in `Check`. Filesystem
operations use pinned directory descriptors and permanently dropped forked workers
(`Sys.Edit`): the privileged Lean process never temporarily adopts a user's ids.
Parent descriptors pin kernel path resolution, including dot/parent components.
As in sudo, links in writable ancestors are refused and the final directory must
not be writable (unless sudoedit_checkdir is disabled); FOLLOW controls final links.
Temporary contents are compared byte-for-byte; original inode metadata detects concurrent edits.
Copy errors preserve the temporary file and attempt to restore the original bytes.
The original inode is retained, so owner/mode and existing hard links survive.
-/
namespace LeanSudo.Sudoedit

private def warn (s : String) : IO Unit := Sys.writeStderr s!"sudoedit: {s}\n"

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

private def resolveEditor (who : Sys.Edit.Identity) (env : Array String)
    (words : List String) : IO (Option String) := do
  unless editorArgsSafe words do return none
  let some word := words.head? | return none
  let path := ((env.toList.find? (·.startsWith "PATH=")).map (fun s => (s.drop 5).toString)).getD "/usr/bin:/bin"
  let paths := if word.startsWith "/" then [word]
    else if word.contains '/' then []
    else (path.splitOn ":").filterMap fun dir =>
      if dir.startsWith "/" then some (dir ++ "/" ++ word) else none
  let self ← Sys.stat "/proc/self/exe"
  for candidate in paths do
    let opened ← try pure (some (← Sys.Edit.operation who 6 Sys.Edit.noneFd candidate).value)
      catch _ => pure none
    if let some fd := opened then
      let st ← try Sys.Edit.stat fd finally Sys.Edit.close fd
      let same := self.any fun s => s.dev == st[7]! && s.ino == st[8]!
      if same || (candidate.splitOn "/").getLast! == "sudoedit" then
        throw (IO.userError "sudoedit may not be used as an editor")
      return some candidate
  return none

private structure Session where
  file : String
  name : String
  parent : UInt32
  temp : String
  original : ByteArray
  originalStat : Array Nat

private def removeTemp (who : Sys.Edit.Identity) (path : String) : IO Unit := do
  let _ ← Sys.Edit.operation who 5 Sys.Edit.noneFd path

private def prepare (invoker target : Sys.Edit.Identity) (follow checkdir : Bool) (file : String) : IO Session := do
  let some (dirs, name) := pathParts file
    | throw (IO.userError s!"{file}: unsafe edit path")
  let parent ← parentDir invoker target checkdir dirs file
  let mut temp := ""
  try
    let fd ← try pure (← Sys.Edit.operation target (if follow then 8 else 1) parent name).value
      catch e => throw (fileError file e)
    let (original, originalStat) ← if fd == Sys.Edit.noneFd then pure (ByteArray.empty, #[])
      else try pure (← Sys.Edit.read fd, ← Sys.Edit.stat fd) finally Sys.Edit.close fd
    let made ← try Sys.Edit.operation invoker 4 Sys.Edit.noneFd s!"/var/tmp/{name}.XXXXXXXX" 0o077
      catch _ => Sys.Edit.operation invoker 4 Sys.Edit.noneFd s!"/tmp/{name}.XXXXXXXX" 0o077
    temp := made.name
    try Sys.Edit.write made.value original ByteArray.empty finally Sys.Edit.close made.value
    return { file, name, parent, temp, original, originalStat }
  catch e =>
    Sys.Edit.close parent
    if temp != "" then
      try removeTemp invoker temp catch _ => pure ()
    throw e

private def copyBack (invoker target : Sys.Edit.Identity) (mask : Nat)
    (follow checkdir : Bool) (s : Session) : IO Bool := do
  try
    let fd ← try pure (← Sys.Edit.operation invoker 1 Sys.Edit.noneFd s.temp).value
      catch e => throw (fileError s.temp e)
    if fd == Sys.Edit.noneFd then throw (IO.userError s!"{s.temp}: No such file or directory")
    let (bytes, checked) ← try
        let st ← Sys.Edit.stat fd
        let checked := tempSafe ((st[0]! &&& Sys.S_IFMT) == 0o100000)
          (st[1]! == invoker.uid.toNat) (st[6]! == 1)
        unless checked do throw (IO.userError s!"{s.temp}: unsafe temporary file")
        pure (← Sys.Edit.read fd, checked)
      finally Sys.Edit.close fd
    let changed := bytes != s.original
    if writeBack changed checked then
      -- Recheck all ancestors as well as the pinned parent: permissions may have
      -- changed while the editor was running. Require the same parent inode.
      let some (dirs, _) := pathParts s.file | throw (IO.userError "unsafe edit path")
      let current ← parentDir invoker target checkdir dirs s.file
      try
        let now ← Sys.Edit.stat current
        let pinned ← Sys.Edit.stat s.parent
        unless now[7]! == pinned[7]! && now[8]! == pinned[8]! do
          throw (IO.userError s!"{s.file}: directory changed during editing")
      finally Sys.Edit.close current
      let out ← try pure (← Sys.Edit.operation target (if follow then 9 else 2) s.parent s.name mask).value
        catch e => throw (fileError s.file e)
      try
        let st ← Sys.Edit.stat out
        unless s.originalStat.isEmpty ||
            (st[7]! == s.originalStat[7]! && st[8]! == s.originalStat[8]! &&
             st[3]! == s.originalStat[3]! && st[4]! == s.originalStat[4]! &&
             st[5]! == s.originalStat[5]!) do
          throw (IO.userError s!"{s.file}: file changed during editing")
        Sys.Edit.write out bytes s.original
      finally Sys.Edit.close out
    else
      warn s!"{s.file} unchanged"
    removeTemp invoker s.temp
    return true
  catch e =>
    warn e.toString
    warn s!"contents of edit session left in {s.temp}"
    return false

/-- Edit `plan.files`; `env` is the editor's environment (`KEY=VALUE`). -/
def run (plan : Core.EditPlan) (env : Array String) : IO Sys.ExitStatus := do
  let mut sessions : Array Session := #[]
  try
    let invoker ← Sys.Edit.identity plan.editUid plan.editGid plan.editGroups
    let target ← Sys.Edit.identity plan.fileUid plan.fileGid plan.fileGroups
    let mut resolved := []
    for words in plan.editors do
      if words.contains "--" then
        throw (IO.userError "editor arguments may not contain \"--\"")
      let result ← resolveEditor invoker env words
      resolved := resolved ++ [(words, result)]
      if result.isSome then break
    let some (path, words) := selectEditor resolved
      | throw (IO.userError s!"no editor found (editor path = {String.intercalate ":" (plan.editors.map (String.intercalate " "))})")
    let mut failed := false
    for file in plan.files do
      try sessions := sessions.push (← prepare invoker target plan.follow plan.checkdir file)
      catch e => warn e.toString; failed := true
    if sessions.isEmpty then return .exited 1
    let status ← try
        Sys.runCommand {
          path := path
          argv := words.toArray ++ sessions.map (·.temp)
          env := env
          uid := plan.editUid
          gid := plan.editGid
          groups := plan.editGroups.toArray
          cwd := none
          umask := plan.umask
          usePty := false
          background := false }
      catch e =>
        for s in sessions do
          warn s!"contents of edit session left in {s.temp}"
        throw e
    for s in sessions do
      unless ← copyBack invoker target plan.umask plan.follow plan.checkdir s do failed := true
    return if failed && status == .exited 0 then .exited 1 else status
  catch e =>
    warn e.toString
    return .exited 1
  finally
    for s in sessions do Sys.Edit.close s.parent

end LeanSudo.Sudoedit
