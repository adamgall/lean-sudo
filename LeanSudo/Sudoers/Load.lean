import LeanSudo.Sudoers.Parser
import LeanSudo.Sys.Core

/-!
# Loading sudoers from disk

Reads `/etc/sudoers`, resolves `@include`/`@includedir` (and the `#` spellings) in
place, and enforces sudo's file-security rules on every file read:

* must be a regular file opened without following symlinks,
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

/-- sudo's ownership/mode policy for sudoers sources. Pure so it can be tested. -/
def checkPerms (path : String) (st : FileStat) : Except String Unit :=
  if !st.isReg then .error s!"{path} is not a regular file"
  else if st.uid != 0 then .error s!"{path} is owned by uid {st.uid}, should be 0"
  else if st.mode &&& 0o002 != 0 then .error s!"{path} is world writable"
  else if st.mode &&& 0o020 != 0 && st.gid != 0 then
    .error s!"{path} is owned by gid {st.gid}, should be 0"
  else .ok ()

/-- Directory part of a path (`/etc/sudoers` ↦ `/etc`). -/
def dirName (path : String) : String :=
  match path.splitOn "/" |>.dropLast with
  | [] => "."
  | [""] => "/"
  | parts => "/".intercalate parts

/-- Expand `%h` (short host name) and `%%`, and resolve relative paths against the
directory of the including file. -/
def resolveIncludePath (including : String) (host : String) (raw : String) : String :=
  let rec expand : List Char → List Char
    | '%' :: 'h' :: rest => host.toList ++ expand rest
    | '%' :: '%' :: rest => '%' :: expand rest
    | c :: rest => c :: expand rest
    | [] => []
  let p := String.ofList (expand raw.toList)
  if p.startsWith "/" then p else dirName including ++ "/" ++ p

/-- sudo skips `@includedir` entries that end in `~` or contain a `.`. -/
def includeDirEntryOk (name : String) : Bool :=
  !name.isEmpty && !name.endsWith "~" && !name.contains '.'

/-- Insertion sort; directory listings are short. Lexical order as sudo uses. -/
def sortNames (xs : List String) : List String :=
  xs.foldl (fun acc x => insert x acc) []
where
  insert (x : String) : List String → List String
    | [] => [x]
    | y :: ys => if decide (x < y) then x :: y :: ys else y :: insert x ys

/-- Outcome of reading one source file. -/
inductive Source where
  | parsed (entries : List Located)
  /-- failed the ownership/mode policy; the message explains why -/
  | insecure (msg : String)

/-- Read and parse one file (no include resolution). Parse errors and unreadable
files throw; ownership/mode violations are reported as `insecure`. -/
def readSource (path : String) : IO Source := do
  let (st, text) ← try readFileNoFollow path
    catch e => throw <| IO.userError s!"unable to open {path}: {e}"
  match checkPerms path st with
  | .error msg => return .insecure msg
  | .ok () =>
    match parse path text with
    | .ok entries => return .parsed entries
    | .error err => throw <| IO.userError err.toString

/-- Directory policy for `@includedir`: a real directory owned by root and not
world-writable (sudo skips the whole directory otherwise). -/
def checkDirPerms (path : String) (st : FileStat) : Except String Unit :=
  if !st.isDir then .error s!"{path} is not a directory"
  else if st.uid != 0 then .error s!"{path} is owned by uid {st.uid}, should be 0"
  else if st.mode &&& 0o002 != 0 then .error s!"{path} is world writable"
  else if st.mode &&& 0o020 != 0 && st.gid != 0 then
    .error s!"{path} is owned by gid {st.gid}, should be 0"
  else .ok ()

mutual
/-- Load `path` and splice includes, depth-bounded.

An *included* file that fails the ownership/mode policy is skipped with a warning
(as sudo does: its contents are attacker-controllable, so neither its grants nor its
denials can be trusted). The main sudoers file failing the policy is fatal. Syntax
errors anywhere are fatal (stricter than sudo, which keeps the parsable part). -/
partial def loadFile (warn : String → IO Unit) (host : String) (depth : Nat) (path : String) :
    IO (List Located) := do
  if depth > maxDepth then
    throw <| IO.userError s!"{path}: too many levels of includes"
  let entries ← match ← readSource path with
    | .parsed es => pure es
    | .insecure msg =>
      if depth == 0 then throw <| IO.userError msg
      else do warn msg; return []
  let mut out : Array Located := #[]
  for loc in entries do
    match loc.entry with
    | .include raw =>
      out := out ++ (← loadFile warn host (depth + 1) (resolveIncludePath path host raw))
    | .includeDir raw =>
      out := out ++ (← loadDir warn host (depth + 1) (resolveIncludePath path host raw))
    | _ => out := out.push loc
  return out.toList

partial def loadDir (warn : String → IO Unit) (host : String) (depth : Nat) (dir : String) :
    IO (List Located) := do
  -- A missing include directory is not an error (sudo ignores it).
  let some st ← lstat dir | return []
  match checkDirPerms dir st with
  | .error msg => warn msg; return []
  | .ok () => pure ()
  let names ← listDir dir
  let mut out : Array Located := #[]
  for name in sortNames (names.filter includeDirEntryOk) do
    out := out ++ (← loadFile warn host depth (dir ++ "/" ++ name))
  return out.toList
end

/-- Load the complete policy starting at `/etc/sudoers` (or `path`). -/
def load (warn : String → IO Unit) (host : String) (path : String := mainSudoersPath) :
    IO (List Located) :=
  loadFile warn host 0 path

end LeanSudo.Sudoers
