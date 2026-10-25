namespace LeanSudo.Sys.Prim.Lookup

@[extern "leansudo_lookup_missing"] opaque missing : Unit → UInt32
@[extern "leansudo_lookup_not_directory"] opaque notDirectory : Unit → UInt32
@[extern "leansudo_lookup_denied"] opaque denied : Unit → UInt32
@[extern "leansudo_lookup_not_permitted"] opaque notPermitted : Unit → UInt32
@[extern "leansudo_lookup_loop"] opaque loop : Unit → UInt32
@[extern "leansudo_lookup_invalid"] opaque invalid : Unit → UInt32
@[extern "leansudo_lookup_io"] opaque io : Unit → UInt32
@[extern "leansudo_lookup_interrupted"] opaque interrupted : Unit → UInt32
@[extern "leansudo_lookup_kill"] opaque kill : Unit → UInt32
@[extern "leansudo_lookup_int_max"] opaque intMax : Unit → UInt32
@[extern "leansudo_lookup_exec_bits"] opaque execBits : Unit → UInt32

end LeanSudo.Sys.Prim.Lookup
