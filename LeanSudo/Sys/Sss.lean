import LeanSudo.Sss

namespace LeanSudo.Sys.Sss

@[extern "leansudo_sss_query"]
opaque query (uid : UInt32) (user : @& String) :
    IO (Array LeanSudo.Sss.Rule × Array LeanSudo.Sss.Rule)

end LeanSudo.Sys.Sss
