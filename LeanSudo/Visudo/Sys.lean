namespace LeanSudo.Visudo

inductive LockResult where
  | locked
  | busy
  | missing
  deriving Repr, BEq, Inhabited

@[extern "leansudo_visudo_lock"] private opaque lockRaw (path : @& String) (mode : UInt32) : IO UInt8

def lockFile (path : String) (mode : UInt32 := 0o440) : IO LockResult := do
  match (← lockRaw path mode) with
  | 0 => pure .locked
  | 1 => pure .busy
  | _ => pure .missing

@[extern "leansudo_visudo_create_temp"]
opaque createTemp (path : @& String) (content : @& String) : IO Unit

@[extern "leansudo_visudo_temp_time"]
opaque copyFileTime (original temp : @& String) : IO Unit

@[extern "leansudo_visudo_modified"]
opaque fileModified (original temp : @& String) : IO Bool

@[extern "leansudo_visudo_export"]
opaque exportSudoers (input output : @& String) : IO Unit

@[extern "leansudo_visudo_run_editor"]
opaque runEditor (path : @& String) (args : @& Array String) : IO Bool

@[extern "leansudo_visudo_set_owner_mode"]
private opaque setOwnerModeRaw (path : @& String) (uid gid mode : UInt32) : IO Unit

def setOwnerMode (path : String) (uid gid mode : Nat) : IO Unit :=
  if uid < 0xFFFFFFFF && gid < 0xFFFFFFFF && mode ≤ 0o7777 then
    setOwnerModeRaw path uid.toUInt32 gid.toUInt32 mode.toUInt32
  else throw (IO.userError s!"invalid owner {uid}:{gid} or mode {mode}")

@[extern "leansudo_visudo_correct_locked_metadata"]
opaque correctLockedMetadata (path : @& String) (uid gid mode : UInt32)
    (owner perms : Bool) : IO Unit

end LeanSudo.Visudo
