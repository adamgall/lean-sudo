/-! System-provided matching oracles. The shell records these facts in the pure
policy request; a failed lookup never grants a policy match. -/
namespace LeanSudo.Sys

@[extern "leansudo_sys_domain"]
opaque domainName : IO (Option String)

@[extern "leansudo_sys_interfaces"]
opaque interfaceAddresses : IO (Array (String × String))

@[extern "leansudo_sys_netgroup"]
opaque inNetgroup (group : @& String) (host user domain : @& Option String) : IO Bool

/-- Sudo's POSIX extended regex dialect: `(?i)` prefix, 1024-byte maximum,
repetition validation and bounds ≤255. Matching uses the administrator's
`sudoers_locale` (C by default), never the caller's message locale.
Invalid expressions raise an error. -/
@[extern "leansudo_sys_regex"]
opaque regexMatches (pattern text : @& String) (locale : @& String := "C") : IO Bool

/-- Expand paths under the same sudoers locale as command regex matching. -/
@[extern "leansudo_sys_glob"]
opaque globPaths (pattern : @& String) (locale : @& String := "C") : IO (List String)

@[extern "leansudo_sys_hostname"]
opaque canonicalHostname (host : @& String) : IO (Option String)

/-- Emit USER_CMD; false is a real audit failure. Unsupported/unavailable kernel
audit is a successful no-op, as in sudo's Linux audit backend. -/
@[extern "leansudo_sys_audit"]
opaque auditCommand (command tty : @& String) (success : Bool) : IO Bool

end LeanSudo.Sys
