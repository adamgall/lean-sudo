/-! System-provided matching oracles. The shell records these facts in the pure
policy request; a failed lookup never grants a policy match. -/
namespace LeanSudo.Sys

@[extern "leansudo_sys_domain"]
opaque domainName : IO (Option String)

@[extern "leansudo_sys_interfaces"]
opaque interfaceAddresses : IO (Array (String × String))

@[extern "leansudo_sys_netgroup"]
opaque inNetgroup (group : @& String) (host user domain : @& Option String) : IO Bool

/-- POSIX extended regex; malformed expressions raise an error, not a non-match. -/
@[extern "leansudo_sys_regex"]
opaque regexMatches (pattern text : @& String) : IO Bool

@[extern "leansudo_sys_glob"]
opaque globPaths (pattern : @& String) : IO (List String)

@[extern "leansudo_sys_hostname"]
opaque canonicalHostname (host : @& String) : IO (Option String)

/-- Emit USER_CMD; false is a real audit failure. Unsupported/unavailable kernel
audit is a successful no-op, as in sudo's Linux audit backend. -/
@[extern "leansudo_sys_audit"]
opaque auditCommand (command tty : @& String) (success : Bool) : IO Bool

end LeanSudo.Sys
