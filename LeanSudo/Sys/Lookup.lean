import LeanSudo.Sys.Core

namespace LeanSudo.Sys.Lookup

def executable (st : FileStat) : Bool :=
  st.isReg && (st.mode &&& 0o111) != 0

theorem executable_iff (st : FileStat) :
    executable st = true ↔ st.isReg = true ∧ (st.mode &&& 0o111) != 0 := by
  simp [executable]

@[extern "lean_sudo_inspect_paths"]
private opaque inspectPathsRaw (paths : @& Array String) (uid gid : UInt32)
    (groups : @& Array UInt32) : IO (Array (Option FileStat))

def inspectPaths (paths : Array String) (uid gid : Nat) (groups : Array Nat) :
    IO (Array (Option FileStat)) := do
  if uid ≥ UInt32.size - 1 || gid ≥ UInt32.size - 1 ||
      groups.any (· ≥ UInt32.size - 1) then
    throw (IO.userError "command lookup: uid or gid out of range")
  inspectPathsRaw paths uid.toUInt32 gid.toUInt32 (groups.map Nat.toUInt32)

end LeanSudo.Sys.Lookup
