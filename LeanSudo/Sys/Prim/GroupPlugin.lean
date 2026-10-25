import LeanSudo.Sys.Prim.Store

namespace LeanSudo.Sys.Prim.GroupPlugin

open Store
@[extern "ls_group_logger"]
opaque logger (callback : UInt32 → String → IO UInt32) : IO Unit
@[extern "ls_group_version"]
opaque version (ptr : Ptr) : IO UInt32
@[extern "ls_group_functions"]
opaque functions (ptr : Ptr) : IO (Ptr × Ptr × Ptr)
@[extern "ls_group_init"]
opaque init (fn args : Ptr) : IO UInt32
@[extern "ls_group_query"]
opaque query (fn : Ptr) (user group : @& String) (passwd : Ptr) : IO UInt32
@[extern "ls_group_cleanup"]
opaque cleanup (fn : Ptr) : IO Unit
@[extern "ls_group_passwd_size"]
opaque passwdSize : Unit → USize
@[extern "ls_group_passwd"]
opaque passwd (name : @& String) (record buffer : Ptr) (size : USize) : IO (UInt32 × Bool)

end LeanSudo.Sys.Prim.GroupPlugin
