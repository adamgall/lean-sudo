import LeanSudo.Sys.Timestamp

/-! Smoke test for `LeanSudo.Sys.Timestamp` / `c/ts.c` (run unprivileged; the root-only
storage path is exercised by the docker integration suite). -/

open LeanSudo LeanSudo.Sys LeanSudo.Timestamp

def check (ok : Bool) (what : String) : IO Unit :=
  if ok then IO.println s!"ok: {what}"
  else throw (IO.userError s!"FAILED: {what}")

def main : IO UInt32 := do
  try
    let now ← bootTimeNanos
    let sid ← getsid
    let ppid ← getppid
    let pid ← IO.Process.getPID
    let selfStart ← processStartTime pid.toNat
    let sidStart ← processStartTime sid
    let ppidStart ← processStartTime ppid
    let tty ← ttyDevice
    IO.println s!"boottime_ns={now} pid={pid} sid={sid} ppid={ppid}"
    IO.println s!"start(self)={selfStart} start(sid)={sidStart} start(ppid)={ppidStart}"
    IO.println s!"tty_dev={tty}"
    let now2 ← bootTimeNanos
    check (now > 0 && now2 ≥ now) "boot clock is positive and monotonic"
    check selfStart.isSome "own start time readable"
    check ppidStart.isSome "parent start time readable"
    check ((← processStartTime 999999999).isNone) "nonexistent pid has no start time"

    -- pure core end-to-end on real values
    let scope := scopeFor .tty tty sid (sidStart.getD 0) ppid (ppidStart.getD 0)
    IO.println s!"scope={repr scope}"
    let rs0 := load ByteArray.empty
    check (!lookup now (some 900) scope 1000 rs0) "empty file grants nothing"
    let rs1 := update now scope 1000 rs0
    let bytes := encode rs1
    IO.println s!"encoded {bytes.size} bytes"
    let rs2 := load bytes
    check (decode bytes == some rs1) "decode ∘ encode = id"
    let later ← bootTimeNanos
    check (lookup later (some 900) scope 1000 rs2) "fresh record is valid"
    check (!lookup later (some 900) scope 0 rs2) "other uid not valid"
    check (!lookup later (some 900) .global 1000 rs2) "other scope not valid"
    check (!lookup later (some 0) scope 1000 rs2) "timeout 0 never valid"
    check (!lookup (later + 901 * 10 ^ 9) (some 900) scope 1000 rs2) "expired after timeout"
    check (!lookup later (some 900) scope 1000 (load (encode (invalidate rs2)))) "-k invalidates"

    -- storage: expected to fail unprivileged
    let r ← (withTimestampFile 1000 fun b => pure ((none : Option ByteArray), b.size)).toBaseIO
    match r with
    | .ok n => IO.println s!"withTimestampFile succeeded (running as root?), {n} bytes"
    | .error e => IO.println s!"withTimestampFile error (expected unprivileged): {e}"
    let r ← (removeTimestampFile 1000).toBaseIO
    match r with
    | .ok _ => IO.println "removeTimestampFile succeeded (running as root?)"
    | .error e => IO.println s!"removeTimestampFile error (expected unprivileged): {e}"
    IO.println "smoke-ts: all checks passed"
    return 0
  catch e =>
    IO.eprintln s!"smoke-ts: {e}"
    return 1
