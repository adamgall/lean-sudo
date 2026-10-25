import LeanSudo.IoLog

namespace LeanSudo.Sys.IoLog

@[extern "leansudo_iolog_clock"]
private opaque clock (formats : @& Array String) (locale : @& String) : IO (Array String)
@[extern "leansudo_iolog_prepare"]
private opaque prepare (dir user group : @& String) (mode maxseq : UInt32) : IO Nat
@[extern "leansudo_iolog_start"]
private opaque start (path legacy json : @& String) (flags : UInt32)
    (patterns : @& Array String) : IO Unit
@[extern "leansudo_iolog_abort"]
private opaque abort : IO Unit

def «open» (p : LeanSudo.IoLog.Plan) (m : LeanSudo.IoLog.Metadata)
    (locale : String) : IO (Option String) := do
  try
    let keys := (LeanSudo.IoLog.timeKeys p.dir.toList ++
      LeanSudo.IoLog.timeKeys p.file.toList).eraseDups
    let facts ← clock keys.toArray locale
    let seconds := (facts[0]!).toNat!
    let nanos := (facts[1]!).toNat!
    let time := keys.zipIdx.map fun (key, n) => (key, facts[n + 4]!)
    let rows := (facts[2]!).toNat!
    let cols := (facts[3]!).toNat!
    let m := { m with rows := if rows == 0 then m.rows else rows
                      cols := if cols == 0 then m.cols else cols }
    let dir := LeanSudo.IoLog.expandPath m "" time p.dir
    let seq ← prepare dir p.user p.group p.mode.toUInt32 p.maxseq.toUInt32
    let file := LeanSudo.IoLog.expandPath m (LeanSudo.IoLog.sequencePath seq) time p.file
    let path := if file.startsWith "/" then file else dir ++ "/" ++ file
    let streams := [p.stdin, p.stdout, p.stderr, p.ttyin, p.ttyout,
      p.compress, p.flush, p.ignoreErrors, p.logPasswords]
    let flags := (streams.zipIdx.foldl (fun (n : Nat) (b, i) => if b then n + 2 ^ i else n) 0).toUInt32
    start path (LeanSudo.IoLog.legacyLog m seconds) (LeanSudo.IoLog.jsonLog m seconds nanos)
      flags p.passpromptRegex
    return some path
  catch e =>
    abort
    if !p.ignoreErrors then throw e
    return none

end LeanSudo.Sys.IoLog
