import LeanSudo.Sss

/-!
# SSSD sudo responder boundary

`c/sss.c` loads the system libsss_sudo ABI used by sudo 1.9.17p2. It only
copies attributes; rule interpretation, filtering and ordering belong to Lean.
-/

namespace LeanSudo.Sys.Sss

/-- Fetch global defaults first, then user rules using the returned SSSD domain.
The second array retains the responder's descending sudoOrder order. Attribute
names and values are copied without interpretation. An unavailable library or
transport yields no rules from that query; malformed results, invalid UTF-8,
allocation failures and other server errors throw instead of returning partial
rules. A username containing NUL is rejected. -/
@[extern "leansudo_sss_query"]
opaque query (uid : UInt32) (user : @& String) :
    IO (Array LeanSudo.Sss.Rule × Array LeanSudo.Sss.Rule)

end LeanSudo.Sys.Sss
