/-!
# `LeanSudo.Visudo.Sys` — FFI bindings to `c/visudo.c`

The few syscalls visudo needs beyond `LeanSudo.Sys.Core`: locking the sudoers file,
creation/truncation of `<file>.tmp`, and fixing its owner/mode before installation.
Errors are `IO.userError`s with `strerror` text.
-/

namespace LeanSudo.Visudo

inductive LockResult where
  | locked
  /-- another process (this visudo or sudo.ws's) holds the lock -/
  | busy
  /-- the missing original was created before taking its lock -/
  | missing
  deriving Repr, BEq, Inhabited

@[extern "leansudo_visudo_lock"] private opaque lockRaw (path : @& String) (mode : UInt32) : IO UInt8

/-- Write-lock every original until exit. OFD locks conflict with sudo.ws's
`F_SETLK` locks and survive the loader's independent reads. -/
def lockFile (path : String) (mode : UInt32 := 0o440) : IO LockResult := do
  match (← lockRaw path mode) with
  | 0 => pure .locked
  | 1 => pure .busy
  | _ => pure .missing

/-- Create or truncate the temporary copy after locking its original. -/
@[extern "leansudo_visudo_create_temp"]
opaque createTemp (path : @& String) (content : @& String) : IO Unit

@[extern "leansudo_visudo_temp_time"]
opaque copyFileTime (original temp : @& String) : IO Unit

@[extern "leansudo_visudo_modified"]
opaque fileModified (original temp : @& String) : IO Bool

/-- Replace this process with the same cvtsudoers invocation as upstream `-x`. -/
@[extern "leansudo_visudo_export"]
opaque exportSudoers (input output : @& String) : IO Unit

/-- Run the editor with inherited credentials/environment. A nonzero exit status
is accepted; termination by signal is not. Parent signal cleanup stays active. -/
@[extern "leansudo_visudo_run_editor"]
opaque runEditor (path : @& String) (args : @& Array String) : IO Bool

@[extern "leansudo_visudo_set_owner_mode"]
private opaque setOwnerModeRaw (path : @& String) (uid gid mode : UInt32) : IO Unit

/-- Open `path` (no symlinks, regular file only), `fchown`, `fchmod`, `fsync`. -/
def setOwnerMode (path : String) (uid gid mode : Nat) : IO Unit :=
  if uid < 0xFFFFFFFF && gid < 0xFFFFFFFF && mode ≤ 0o7777 then
    setOwnerModeRaw path uid.toUInt32 gid.toUInt32 mode.toUInt32
  else throw (IO.userError s!"invalid owner {uid}:{gid} or mode {mode}")

end LeanSudo.Visudo
