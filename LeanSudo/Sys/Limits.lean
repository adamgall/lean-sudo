import Lean
import LeanSudo.Sys.Prim.Exec

namespace LeanSudo.Sys.Limits

open Prim.Exec

structure Entry where
  name : String
  resource : UInt32
  override : Bool
  minimum : UInt64
  target : UInt64 × UInt64
  fallback : Option (UInt64 × UInt64) := none

structure Saved where
  entry : Entry
  original : UInt64 × UInt64
  override : Bool
  target : UInt64 × UInt64

private initialize savedLimits : IO.Ref (Option (Array Saved)) ← IO.mkRef none
private initialize savedNproc : IO.Ref (UInt64 × UInt64) ← IO.mkRef (0, 0)

private def openMax : UInt64 := 256

private def stackMinimum : UInt64 :=
  if USize.size == 18446744073709551616 then 4 * 1024 * 1024 else 2 * 1024 * 1024

def entries : Array Entry :=
  let infinity := K.RLIM_INFINITY ()
  let unlimited := (infinity, infinity)
  #[{ name := "rlimit_as", resource := K.RLIMIT_AS (), override := true,
      minimum := 1024 * 1024 * 1024, target := unlimited },
    { name := "rlimit_core", resource := K.RLIMIT_CORE (), override := false,
      minimum := infinity, target := unlimited },
    { name := "rlimit_cpu", resource := K.RLIMIT_CPU (), override := true,
      minimum := infinity, target := unlimited },
    { name := "rlimit_data", resource := K.RLIMIT_DATA (), override := true,
      minimum := 1024 * 1024 * 1024, target := unlimited },
    { name := "rlimit_fsize", resource := K.RLIMIT_FSIZE (), override := true,
      minimum := infinity, target := unlimited },
    { name := "rlimit_locks", resource := K.RLIMIT_LOCKS (), override := false,
      minimum := infinity, target := unlimited },
    { name := "rlimit_memlock", resource := K.RLIMIT_MEMLOCK (), override := false,
      minimum := infinity, target := unlimited },
    { name := "rlimit_nofile", resource := K.RLIMIT_NOFILE (), override := true,
      minimum := openMax, target := (openMax, infinity) },
    { name := "rlimit_nproc", resource := K.RLIMIT_NPROC (), override := true,
      minimum := infinity, target := unlimited },
    { name := "rlimit_rss", resource := K.RLIMIT_RSS (), override := true,
      minimum := infinity, target := unlimited },
    { name := "rlimit_stack", resource := K.RLIMIT_STACK (), override := true,
      minimum := stackMinimum, target := (stackMinimum, infinity),
      fallback := some (stackMinimum, 65532 * 1024) }]

def warn (progname message : String) (error : UInt32) : IO Unit := do
  try writeAll 2 s!"{progname}: {message}: {← strerror error}\n".toUTF8 catch _ => pure ()

private def keepLarger (old target : UInt64 × UInt64) : UInt64 × UInt64 :=
  let infinity := K.RLIM_INFINITY ()
  let current := if target.1 != infinity && (old.1 == infinity || old.1 > target.1) then old.1
    else target.1
  let maximum := if target.2 != infinity && (old.2 == infinity || old.2 > target.2) then old.2
    else target.2
  (current, maximum)

private def raise (entry : Entry) (old : UInt64 × UInt64) : IO (UInt64 × UInt64 × UInt32) := do
  let mut target := keepLarger old entry.target
  let mut error ← setrlimit entry.resource target.1 target.2
  if error != 0 then
    if let some fallback := entry.fallback then
      target := keepLarger old fallback
      error ← setrlimit entry.resource target.1 target.2
  if error != 0 then
    target := (old.2, old.2)
    error ← setrlimit entry.resource target.1 target.2
  return (target.1, target.2, error)

def unlimit (progname : String) : IO Unit := do
  if (← savedLimits.get).isSome then return
  let infinity := K.RLIM_INFINITY ()
  let mut saved := #[]
  for entry in entries do
    let some old ← try pure (some (← getrlimit entry.resource)) catch _ => pure none
      | continue
    let override := entry.override && (entry.minimum == infinity || old.1 < entry.minimum)
    let mut target := entry.target
    if override then
      let (current, maximum, error) ← raise entry old
      target := (current, maximum)
      if error != 0 then warn progname s!"setrlimit({entry.name})" error
    saved := saved.push { entry, original := old, override, target }
  savedLimits.set (some saved)

def original (resource : UInt32) : IO (Option (UInt64 × UInt64)) := do
  match (← savedLimits.get) with
  | some saved => return (saved.find? (·.entry.resource == resource)).map (·.original)
  | none => try pure (some (← getrlimit resource)) catch _ => pure none

structure Restoration where
  name : String
  resource : Nat
  current : Nat
  maximum : Nat
  cap : Nat
  deriving Lean.ToJson, Lean.FromJson

def pending : IO (Array Restoration) := do
  let some saved ← savedLimits.get | return #[]
  return saved.filterMap fun limit => if !limit.override then none else some {
    name := limit.entry.name, resource := limit.entry.resource.toNat
    current := limit.original.1.toNat, maximum := limit.original.2.toNat
    cap := limit.target.1.toNat }

private def restoreOne (item : Restoration) : IO UInt32 := do
  let infinity := K.RLIM_INFINITY ()
  let resource := item.resource.toUInt32
  let cap := item.cap.toUInt64
  let mut limit := (item.current.toUInt64, item.maximum.toUInt64)
  let mut error := 0
  for _ in [:10] do
    error ← setrlimit resource limit.1 limit.2
    if error == 0 || error != K.EINVAL () then break
    if limit.1 > 0x7FFFFFFFFFFFFFFF / 2 then break
    let doubled := limit.1 * 2
    let current := if cap != infinity && doubled > cap then cap else doubled
    let maximum := if limit.2 != infinity && current > limit.2 then current else limit.2
    limit := (current, maximum)
    error ← setrlimit resource limit.1 limit.2
    if error == 0 || error != K.EINVAL () then break
  return error

def restoreFrom (progname : String) (items : Array Restoration) : IO Unit := do
  for item in items do
    let error ← restoreOne item
    if error != 0 then warn progname s!"setrlimit({item.name})" error

def restore (progname : String) : IO Unit := do
  restoreFrom progname (← pending)

def unlimitNproc (progname : String) : IO Unit := do
  let infinity := K.RLIM_INFINITY ()
  try savedNproc.set (← getrlimit (K.RLIMIT_NPROC ())) catch error =>
    try writeAll 2 s!"{progname}: getrlimit(RLIMIT_NPROC): {error}\n".toUTF8 catch _ => pure ()
  if (← setrlimit (K.RLIMIT_NPROC ()) infinity infinity) != 0 then
    let maximum := (← savedNproc.get).2
    let error ← setrlimit (K.RLIMIT_NPROC ()) maximum maximum
    if error != 0 then warn progname "setrlimit(RLIMIT_NPROC)" error

def restoreNproc (progname : Option String) : IO Unit := do
  let (current, maximum) ← savedNproc.get
  let error ← setrlimit (K.RLIMIT_NPROC ()) current maximum
  if let some progname := progname then
    if error != 0 then warn progname "setrlimit(RLIMIT_NPROC)" error

end LeanSudo.Sys.Limits
