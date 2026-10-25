namespace LeanSudo.Sys.Prim.Visudo

@[extern "leansudo_visudo_default_path"] opaque defaultPath : IO (UInt32 × USize × String)
@[extern "leansudo_visudo_ENOTDIR"] opaque ENOTDIR : Unit → UInt32
@[extern "leansudo_visudo_ESTALE"] opaque ESTALE : Unit → UInt32
@[extern "leansudo_visudo_ENODEV"] opaque ENODEV : Unit → UInt32

end LeanSudo.Sys.Prim.Visudo
