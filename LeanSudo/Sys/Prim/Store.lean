namespace LeanSudo.Sys.Prim.Store

abbrev Ptr := UInt64

structure Constants where
  dlNow : UInt32
  dlLazy : UInt32
  dlGlobal : UInt32
  dlLocal : UInt32
  eio : UInt32
  enoent : UInt32
  econnrefused : UInt32
  econnreset : UInt32
  enotconn : UInt32
  etimedout : UInt32
  epipe : UInt32
  ehostunreach : UInt32
  enetunreach : UInt32
  enetdown : UInt32
  eagain : UInt32
  eproto : UInt32
  eilseq : UInt32
  einval : UInt32
  enosys : UInt32
  enametoolong : UInt32
  intMax : UInt32
  pointerSize : UInt32
  pathMax : UInt32
  deriving Inhabited

@[extern "ls_store_constants"]
opaque constants (_ : Unit) : Constants

private initialize cached : IO.Ref (Option Constants) ← IO.mkRef none

def native : IO Constants := do
  if let some value ← cached.get then return value
  let value := constants ()
  cached.set (some value)
  return value

@[extern "ls_store_dlopen"]
opaque dlopen (path : @& String) (flags : UInt32) : IO Ptr
@[extern "ls_store_dlsym"]
opaque dlsym (handle : Ptr) (name : @& String) : IO Ptr
@[extern "ls_store_dlclose"]
opaque dlclose (handle : Ptr) : IO Unit
@[extern "ls_store_dlerror"]
private opaque dlerrorRaw : IO (Option String)

def dlerror : IO String := return (← dlerrorRaw).getD "unknown error"
@[extern "ls_store_free"]
opaque free (ptr : Ptr) : IO Unit
@[extern "ls_store_calloc"]
opaque calloc (count size : USize) : IO Ptr
@[extern "ls_store_strdup"]
opaque strdup (text : @& String) : IO Ptr
@[extern "ls_store_pointer"]
opaque pointer (ptr : Ptr) (index : USize) : IO Ptr
@[extern "ls_store_set_pointer"]
opaque setPointer (ptr : Ptr) (index : USize) (value : Ptr) : IO Unit
@[extern "ls_store_bytes"]
opaque bytes (ptr : Ptr) : IO ByteArray
@[extern "ls_store_strerror"]
opaque strerror (error : UInt32) : IO String

end LeanSudo.Sys.Prim.Store
