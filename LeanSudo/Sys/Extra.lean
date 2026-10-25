import LeanSudo.Sys.Core

namespace LeanSudo.Sys

@[extern "leansudo_sys_domain"]
opaque domainName : IO (Option String)

@[extern "leansudo_sys_interfaces"]
opaque interfaceAddresses : IO (Array (String × String))

@[extern "leansudo_sys_netgroup"]
opaque inNetgroup (group : @& String) (host user domain : @& Option String) : IO Bool

@[extern "leansudo_sys_regex"]
opaque regexMatches (pattern text : @& String) (locale : @& String := "C") : IO Bool

@[extern "leansudo_sys_glob"]
opaque globPaths (pattern : @& String) (locale : @& String := "C") : IO (List String)

@[extern "leansudo_sys_hostname"]
opaque canonicalHostname (host : @& String) : IO (Except String String)

@[extern "leansudo_sys_audit"]
opaque auditCommand (command tty : @& String) (success : Bool) : IO Bool

def commandLookupRoot (root : Option String) : Option String :=
  root.filter (· != "*")

theorem commandLookupRoot_wildcard : commandLookupRoot (some "*") = none := by
  rfl

theorem wildcard_lookup_path (path : String) :
    ((commandLookupRoot (some "*")).map (· ++ path)).getD path = path := by
  rfl

def withinRoot (root path : String) : Bool :=
  root == "/" || path == root || path.startsWith (root ++ "/")

theorem withinRoot_boundary (root path : String) (hr : root ≠ "/")
    (hp : path ≠ root) (h : withinRoot root path = true) :
    path.startsWith (root ++ "/") = true := by
  simpa [withinRoot, hr, hp] using h

def rootPathEscapes (root path : String) : IO Bool := do
  let canonical := (← realpath root).getD root
  let some resolved ← realpath (root ++ path) | return false
  return !withinRoot canonical resolved

end LeanSudo.Sys
