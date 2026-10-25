import LeanSudo.Sudoers.Parser
import LeanSudo.Sys.Core

/-!
# Loading sudoers from disk

Reads `/etc/sudoers`, resolves `@include`/`@includedir` (and the `#` spellings) in
place, and enforces sudo's file-security rules on every file read:

* must be a regular file (symlinks followed, metadata checked on the opened fd),
* owned by uid 0,
* not world-writable, and if group-writable then owned by gid 0.

Any violation, unreadable `@include` target, parse error, or include depth above
`maxDepth` aborts loading (fail-closed): sudo then refuses to run.
-/

namespace LeanSudo.Sudoers

open LeanSudo.Sys

def mainSudoersPath : String := "/etc/sudoers"

/-- Maximum include nesting, as in sudo. -/
def maxDepth : Nat := 128

private def checkOwnership (kind : Bool) (what path : String) (st : FileStat) :
    Except String Unit :=
  if !kind then .error s!"{path} is not {what}"
  else if st.uid != 0 then .error s!"{path} is owned by uid {st.uid}, should be 0"
  else if st.mode &&& 0o002 != 0 then .error s!"{path} is world writable"
  else if st.mode &&& 0o020 != 0 && st.gid != 0 then
    .error s!"{path} is owned by gid {st.gid}, should be 0"
  else .ok ()

/-- sudo's ownership/mode policy for sudoers sources. Pure so it can be tested. -/
def checkPerms (path : String) (st : FileStat) : Except String Unit :=
  checkOwnership st.isReg "a regular file" path st

/-- Directory part of a path (`/etc/sudoers` ↦ `/etc`). -/
def dirName (path : String) : String :=
  match path.splitOn "/" |>.dropLast with
  | [] => "."
  | [""] => "/"
  | parts => "/".intercalate parts

/-- Expand `%h` (short host name), and resolve relative paths against the
directory of the including file. -/
def resolveIncludePath (including : String) (host : String) (raw : String) : String :=
  let rec expand : List Char → List Char
    | '%' :: 'h' :: rest => host.toList ++ expand rest
    | c :: rest => c :: expand rest
    | [] => []
  let p := String.ofList (expand raw.toList)
  if p.startsWith "/" then p else dirName including ++ "/" ++ p

/-- sudo skips `@includedir` entries that end in `~` or contain a `.`. -/
def includeDirEntryOk (name : String) : Bool :=
  !name.isEmpty && !name.endsWith "~" && !name.contains '.'

/-- Directory policy for `@includedir`: a real directory owned by root, not
world-writable, and group-writable only when owned by gid 0. Violations are fatal. -/
def checkDirPerms (path : String) (st : FileStat) : Except String Unit :=
  checkOwnership st.isDir "a directory" path st

mutual
/-- Load `path` and splice includes, depth-bounded.

Ownership/mode violations and syntax errors anywhere are fatal. Skipping an
insecure included source could discard a denial and widen the policy. -/
partial def loadFile (host : String) (depth : Nat) (path : String) :
    IO (List Located) := do
  if depth > maxDepth then
    throw <| IO.userError s!"{path}: too many levels of includes"
  let (st, text) ← try readFileFollow path
    catch e => throw <| IO.userError s!"unable to open {path}: {e}"
  IO.ofExcept (checkPerms path st)
  let entries ← IO.ofExcept (parse path text)
  let mut out : Array Located := #[]
  for loc in entries do
    for warning in loc.warnings do writeStderr (warning ++ "\n")
    match loc.entry with
    | .include raw =>
      out := out ++ (← loadFile host (depth + 1) (resolveIncludePath path host raw))
    | .includeDir raw =>
      out := out ++ (← loadDir host (depth + 1) (resolveIncludePath path host raw))
    | _ => out := out.push loc
  return out.toList

partial def loadDir (host : String) (depth : Nat) (dir : String) :
    IO (List Located) := do
  -- A missing include directory is not an error (sudo ignores it).
  let some st ← stat dir | return []
  match checkDirPerms dir st with
  | .error msg => throw <| IO.userError msg
  | .ok () => pure ()
  let names ← listDir dir
  let mut out : Array Located := #[]
  for name in (names.filter includeDirEntryOk).mergeSort (· < ·) do
    let path := dir ++ "/" ++ name
    let some st ← stat path | continue
    if st.isReg then out := out ++ (← loadFile host depth path)
  return out.toList
end

/-- Load the complete policy starting at `/etc/sudoers` (or `path`). -/
def load (host : String) (path : String := mainSudoersPath) :
    IO (List Located) :=
  loadFile host 0 path

end LeanSudo.Sudoers
