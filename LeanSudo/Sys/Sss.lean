import LeanSudo.Sss
import LeanSudo.Sys.Prim.Sss
import LeanSudo.Sys.Prim.CoreLogs

namespace LeanSudo.Sys.Sss

open Prim.Store

private structure Api where
  rules : Ptr
  defaults : Ptr
  freeResult : Ptr
  values : Ptr
  freeValues : Ptr

private def failure {α : Type} (operation : String) (error : UInt32) : IO α := do
  throw (IO.userError s!"SSSD {operation}: {← strerror error}")

def requestError (native : Constants) (rc server saved : UInt32) : UInt32 :=
  if server > 0 then if server ≤ native.intMax then server else native.eio
  else if rc > 0 && rc ≤ native.intMax then rc
  else if saved != 0 then saved else native.eio

theorem requestError_server (native : Constants) (rc server saved : UInt32)
    (positive : server > 0) (bounded : server ≤ native.intMax) :
    requestError native rc server saved = server := by
  simp [requestError, positive, bounded]

private def unavailable (native : Constants) (error : UInt32) : Bool :=
  [native.enoent, native.econnrefused, native.econnreset, native.enotconn,
    native.etimedout, native.epipe, native.ehostunreach, native.enetunreach,
    native.enetdown, native.eagain].contains error

private def openLibrary (native : Constants) : IO Ptr := do
  let (error, architecture) ← Prim.CoreLogs.uname
  let machine := if error == 0 && (architecture == "x86_64" || architecture == "aarch64") then
    architecture ++ "-linux-gnu" else ""
  let paths := (if machine.isEmpty then [] else [s!"/usr/lib/{machine}/libsss_sudo.so"]) ++
    ["/usr/lib64/libsss_sudo.so", "/usr/lib/libsss_sudo.so", "libsss_sudo.so", "libsss_sudo.so.0"]
  for path in paths do
    let handle ← dlopen path (native.dlNow ||| native.dlLocal)
    if handle != 0 then return handle
  return 0

private def loadApi (native : Constants) (handle : Ptr) : IO Api := do
  let names := #["sss_sudo_send_recv", "sss_sudo_send_recv_defaults", "sss_sudo_free_result",
    "sss_sudo_get_values", "sss_sudo_free_values"]
  let mut symbols := #[]
  for name in names do
    let fn ← dlsym handle name
    if fn == 0 then failure "library ABI" native.enosys
    symbols := symbols.push fn
  return {
    rules := symbols[0]!
    defaults := symbols[1]!
    freeResult := symbols[2]!
    values := symbols[3]!
    freeValues := symbols[4]! }

private def string (native : Constants) (operation : String) (ptr : Ptr) : IO String := do
  if ptr == 0 then failure operation native.eproto
  match String.fromUTF8? (← bytes ptr) with
  | some text => return text
  | none => failure operation native.eilseq

private def copyResult (native : Constants) (api : Api) (operation : String) (result : Ptr) :
    IO (Array LeanSudo.Sss.Rule) := do
  if result == 0 then failure operation native.eproto
  let (count, rules) ← Prim.Sss.result result
  if count != 0 && rules == 0 then failure operation native.eproto
  let mut copied := Array.mkEmpty count.toNat
  for i in [:count.toNat] do
    let (count, attrs) ← Prim.Sss.rule rules i.toUInt32
    if count != 0 && attrs == 0 then failure operation native.eproto
    let mut rule := Array.mkEmpty count.toNat
    for j in [:count.toNat] do
      let (name, capacity) ← Prim.Sss.attr attrs j.toUInt32
      let name ← string native operation name
      let (error, values) ← Prim.Sss.values api.values attrs j.toUInt32
      try
        if error != 0 then failure operation error
        if values == 0 then failure operation native.eproto
        let mut copiedValues := Array.mkEmpty capacity.toNat
        let mut index := 0
        repeat
          let value ← pointer values index.toUSize
          if value == 0 then break
          copiedValues := copiedValues.push (← string native operation value)
          index := index + 1
        rule := rule.push (name, copiedValues)
      finally
        if values != 0 then Prim.Sss.freeValues api.freeValues values
    copied := copied.push rule
  return copied

private def response (native : Constants) (api : Api) (operation : String) (rc saved server : UInt32)
    (result : Ptr) : IO (Array LeanSudo.Sss.Rule) := do
  if rc != 0 then
    let error := requestError native rc server saved
    if unavailable native error then return #[]
    failure operation error
  else if server == 0 then copyResult native api operation result
  else if server == native.enoent then return #[]
  else failure operation (if server ≤ native.intMax then server else native.eio)

def query (uid : UInt32) (user : String) :
    IO (Array LeanSudo.Sss.Rule × Array LeanSudo.Sss.Rule) := do
  let native ← native
  if user.isEmpty || user.contains '\x00' then failure "username" native.einval
  let handle ← openLibrary native
  if handle == 0 then return (#[], #[])
  try
    let api ← loadApi native handle
    let ((rc, saved), server, domain, result) ← Prim.Sss.defaults api.defaults uid user
    try
      let defaults ← try response native api "defaults query" rc saved server result
        finally Prim.Sss.freeResult api.freeResult result
      let ((rc, saved), server, result) ← Prim.Sss.rules api.rules uid user domain
      let rules ← try response native api "rules query" rc saved server result
        finally Prim.Sss.freeResult api.freeResult result
      return (defaults, rules)
    finally free domain
  finally dlclose handle

end LeanSudo.Sys.Sss
