import LeanSudo.Sys.Core

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

/-- Resolve AI_CANONNAME; resolver failures retain gai_strerror for sudo's warning. -/
@[extern "leansudo_sys_hostname"]
opaque canonicalHostname (host : @& String) : IO (Except String String)

/-- Emit USER_CMD; false is a real audit failure. Unsupported/unavailable kernel
audit is a successful no-op, as in sudo's Linux audit backend. -/
@[extern "leansudo_sys_audit"]
opaque auditCommand (command tty : @& String) (success : Bool) : IO Bool

/-- Directory containment uses a component boundary, never a bare string prefix. -/
def withinRoot (root path : String) : Bool :=
  root == "/" || path == root || path.startsWith (root ++ "/")

theorem withinRoot_boundary (root path : String) (hr : root ≠ "/")
    (hp : path ≠ root) (h : withinRoot root path = true) :
    path.startsWith (root ++ "/") = true := by
  simpa [withinRoot, hr, hp] using h

/-- Prefix lookup must not follow a symlink or parent component outside the jail.
Missing paths are handled by command lookup/exec, not confused with an escape. -/
def rootPathEscapes (root path : String) : IO Bool := do
  let canonical := (← realpath root).getD root
  let some resolved ← realpath (root ++ path) | return false
  return !withinRoot canonical resolved

end LeanSudo.Sys
