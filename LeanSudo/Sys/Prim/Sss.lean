import LeanSudo.Sys.Prim.Store

namespace LeanSudo.Sys.Prim.Sss

open Store

@[extern "ls_sss_defaults"]
opaque defaults (fn : Ptr) (uid : UInt32) (user : @& String) :
    IO ((UInt32 × UInt32) × UInt32 × Ptr × Ptr)
@[extern "ls_sss_rules"]
opaque rules (fn : Ptr) (uid : UInt32) (user : @& String) (domain : Ptr) :
    IO ((UInt32 × UInt32) × UInt32 × Ptr)
@[extern "ls_sss_free_result"]
opaque freeResult (fn ptr : Ptr) : IO Unit
@[extern "ls_sss_result"]
opaque result (ptr : Ptr) : IO (UInt32 × Ptr)
@[extern "ls_sss_rule"]
opaque rule (ptr : Ptr) (index : UInt32) : IO (UInt32 × Ptr)
@[extern "ls_sss_attr"]
opaque attr (ptr : Ptr) (index : UInt32) : IO (Ptr × UInt32)
@[extern "ls_sss_values"]
opaque values (fn ptr : Ptr) (index : UInt32) : IO (UInt32 × Ptr)
@[extern "ls_sss_free_values"]
opaque freeValues (fn ptr : Ptr) : IO Unit

end LeanSudo.Sys.Prim.Sss
