import LeanSudo.Sys.Core

/-!
# Credential-scoped command lookup

`inspectPaths` gathers `stat(2)` facts in one permanently privilege-dropped child
per credential set. It does not test `access(X_OK)`: sudo.ws `goodpath.c` accepts
any regular file with any execute bit. Search order, dot handling and fallback
from the run-as credentials to invoking credentials remain in Lean. In particular,
sudo.ws `resolve_cmnd.c` retries only a missing result, not an ignored-dot result.
The caller must still canonicalize the parent and use the existing pinned-file
policy/execution workflow; these lookup facts do not authorize execution.
-/

namespace LeanSudo.Sys.Lookup

/-- sudo.ws's `sudo_goodpath` criterion, independent of the inspecting uid. -/
def executable (st : FileStat) : Bool :=
  st.isReg && (st.mode &&& 0o111) != 0

theorem executable_iff (st : FileStat) :
    executable st = true ↔ st.isReg = true ∧ (st.mode &&& 0o111) != 0 := by
  simp [executable]

@[extern "lean_sudo_inspect_paths"]
private opaque inspectPathsRaw (paths : @& Array String) (uid gid : UInt32)
    (groups : @& Array UInt32) : IO (Array (Option FileStat))

/-- Inspect every path in order with exactly these real/effective/saved ids and
supplementary groups. A missing, inaccessible, non-directory-component or looping
path returns `none`; any other stat error, invalid id/NUL, credential-switch
failure, resource exhaustion or malformed/incomplete child reply throws.

The array has exactly one entry per path, including non-regular files. Each call
uses one child, not one child per path. At most 65,536 paths and supplementary
groups are accepted; exceeding either bound is an error, never a partial search.
No parent credentials are changed. -/
def inspectPaths (paths : Array String) (uid gid : Nat) (groups : Array Nat) :
    IO (Array (Option FileStat)) := do
  if uid ≥ UInt32.size - 1 || gid ≥ UInt32.size - 1 ||
      groups.any (· ≥ UInt32.size - 1) then
    throw (IO.userError "command lookup: uid or gid out of range")
  inspectPathsRaw paths uid.toUInt32 gid.toUInt32 (groups.map Nat.toUInt32)

end LeanSudo.Sys.Lookup
