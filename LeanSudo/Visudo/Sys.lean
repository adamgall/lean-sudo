/-!
# `LeanSudo.Visudo.Sys` — FFI bindings to `c/visudo.c`

The few syscalls visudo needs beyond `LeanSudo.Sys.Core`: locking the sudoers file,
exclusive creation of `<file>.tmp`, and fixing its owner/mode before installation.
Errors are `IO.userError`s with `strerror` text.
-/

namespace LeanSudo.Visudo

inductive LockResult where
  | locked
  /-- another process (this visudo or sudo.ws's) holds the lock -/
  | busy
  /-- the file does not exist (a new sudoers file is being created) -/
  | missing
  deriving Repr, BEq, Inhabited

@[extern "leansudo_visudo_lock"] private opaque lockRaw (path : @& String) : IO UInt8

/-- Write-lock `path` (`F_OFD_SETLK`; conflicts with sudo.ws's `F_SETLK` lock). The lock
is held until the process exits. Symlinks are refused. -/
def lockFile (path : String) : IO LockResult := do
  match (← lockRaw path) with
  | 0 => pure .locked
  | 1 => pure .busy
  | _ => pure .missing

/-- Create `path` exclusively (`O_CREAT|O_EXCL`, mode 0600) holding `content`, fsynced.
`false` if it already exists. -/
@[extern "leansudo_visudo_create_excl"]
opaque createExcl (path : @& String) (content : @& String) : IO Bool

@[extern "leansudo_visudo_set_owner_mode"]
private opaque setOwnerModeRaw (path : @& String) (uid gid mode : UInt32) : IO Unit

/-- Open `path` (no symlinks, regular file only), `fchown`, `fchmod`, `fsync`. -/
def setOwnerMode (path : String) (uid gid mode : Nat) : IO Unit :=
  if uid < 0xFFFFFFFF && gid < 0xFFFFFFFF && mode ≤ 0o7777 then
    setOwnerModeRaw path uid.toUInt32 gid.toUInt32 mode.toUInt32
  else throw (IO.userError s!"invalid owner {uid}:{gid} or mode {mode}")

end LeanSudo.Visudo
