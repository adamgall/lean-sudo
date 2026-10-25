import LeanSudo.Sys.Exec
import LeanSudo.Sys.Extra

/-!
# Smoke test for `LeanSudo.Sys.Exec` (runs unprivileged)

`lake exe smoke-exec` runs every case as a fresh sub-process of itself
(`smoke-exec case <name> …`) so that the command's output (which goes straight to
the inherited fds) and our own exit/stop behaviour can be observed from outside.
Pty cases run the binary under `script(1)` to obtain a controlling terminal
(`script -qec '<self> pty …' /dev/null`). Exit code 0 ⇔ all checks passed.
-/

open LeanSudo.Sys

namespace SmokeExec

#guard Exec.validExecFd none
#guard Exec.validExecFd (some 3)
#guard !Exec.validExecFd (some 2)
#guard !Exec.validExecFd (some 0xFFFFFFFF)

structure Ids where
  uid : Nat
  gid : Nat
  groups : Array Nat

/-- Own ids from /proc (no dependency on `Sys.Core`). -/
def ownIds : IO Ids := do
  let st ← IO.FS.readFile "/proc/self/status"
  let field (k : String) : List Nat :=
    match (st.splitOn "\n").find? (·.startsWith (k ++ ":")) with
    | some l => ((l.drop (k.length + 1)).split (fun c => c == '\t' || c == ' ')).toList.filterMap
        (fun s => s.toString.toNat?)
    | none => []
  pure { uid := (field "Uid").headD 0, gid := (field "Gid").headD 0,
         groups := (field "Groups").toArray }

def spec (ids : Ids) (path : String) (argv : Array String) : ExecSpec :=
  { path, argv, env := #["PATH=/usr/bin:/bin"], uid := ids.uid, gid := ids.gid,
    groups := ids.groups, cwd := none, umask := 0o022, usePty := false, background := false }

#guard !(spec ⟨1000, 1000, #[]⟩ "/bin/true" #["true"]).staySetuid
#guard (Exec.check { spec ⟨1000, 1000, #[]⟩ "/bin/true" #["true"] with
    staySetuid := true }).isOk
#guard !(Exec.check { spec ⟨4294967295, 1000, #[]⟩ "/bin/true" #["true"] with
    staySetuid := true }).isOk
#guard (Exec.check { spec ⟨1000, 1000, #[]⟩ "/bin/true" #["true"] with
    chroot := some "/srv/jail" }).isOk
#guard !(Exec.check { spec ⟨1000, 1000, #[]⟩ "/bin/true" #["true"] with
    chroot := some "/srv/jail\x00outside" }).isOk
#guard withinRoot "/" "/usr/bin/id"
#guard withinRoot "/srv/jail" "/srv/jail/bin/sh"
#guard withinRoot "/srv/jail" "/srv/jail"
#guard !withinRoot "/srv/jail" "/srv/jail-other/bin/sh"
#guard !withinRoot "/srv/jail" "/usr/bin/sh"

def fmtStatus : ExitStatus → String
  | .exited c => s!"exited {c}"
  | .signaled s => s!"signaled {s}"

/-- Run and print `STATUS …` / `ERROR …` after whatever the command printed. -/
def report (s : ExecSpec) : IO Unit := do
  try
    let st ← runCommand s
    IO.println s!"STATUS {fmtStatus st}"
  catch e =>
    IO.println s!"ERROR {e}"
  (← IO.getStdout).flush

/-! ## Sub-process side -/

def runCase (name : String) (rest : List String) : IO Unit := do
  let ids ← ownIds
  let sh (script : String) := spec ids "/bin/sh" #["sh", "-c", script]
  match name, rest with
  -- generic: `case run <usePty 0|1> <path> argv…` (manual experiments)
  | "run", usePty :: path :: argv =>
    report { spec ids path argv.toArray with usePty := usePty == "1" }
  | "id", _ => report (spec ids "/usr/bin/id" #["id"])
  | "exit7", _ => report (sh "exit 7")
  | "exit7pty", _ => report { sh "exit 7" with usePty := true }
  | "ptypipe", _ =>
    report { sh "test -t 1 || echo stdout-is-pipe; test -t 0 && echo stdin-is-tty; exit 0" with
      usePty := true }
  | "term", _ => report (sh "kill -TERM $$")
  | "noent", _ => report (spec ids "/nonexistent/lean-sudo-smoke" #["x"])
  | "file", [f] => report (spec ids f #["script-argv0", "arg1"])
  | "env", _ => report { spec ids "/usr/bin/env" #["env"] with env := #["FOO=bar", "SPACE=a b"] }
  | "cwd", [d] => report { spec ids "/bin/pwd" #["pwd"] with cwd := some d }
  | "cwdOptional", _ => report { sh "echo continued" with
      cwd := some "/nonexistent-dir", cwdOptional := true }
  | "corelimit", _ => report (sh "ulimit -c")
  | "timeout", _ => report { sh "exec sleep 10" with timeout := 1 }
  | "missing-noexec", _ => report { sh "echo must-not-run" with
      noexecFile := some "/nonexistent/lean-sudo-noexec.so" }
  | "badapparmor", _ => report { sh "true" with apparmorProfile := some "bad\x00profile" }
  | "umask", _ => report { sh "umask" with umask := 0o027 }
  | "closefrom", [n] =>
    -- fd 5 is opened (without CLOEXEC) by the wrapping shell
    let fds ← System.FilePath.readDir "/proc/self/fd"
    IO.println s!"PARENT_HAS_5 {fds.any (·.fileName == "5")}"
    report { spec ids "/bin/ls" #["ls", "/proc/self/fd"] with closeFrom := n.toNat! }
  | "uid", [n, marker] => report { sh s!"touch {marker}" with uid := n.toNat! }
  | "gid", [n, marker] => report { sh s!"touch {marker}" with gid := n.toNat! }
  | "groups", [marker] => report { sh s!"touch {marker}" with groups := #[0] }
  | "baduid", _ => report { sh "true" with uid := 4294967295 }
  | "nul", _ => report (sh "echo a\x00b")
  | "relpath", _ => report (spec ids "bin/sh" #["sh"])
  | "background", [f] =>
    report { sh s!"sleep 0.5; echo bg-done > {f}" with background := true }
  | "signals", _ =>
    report (sh "trap 'echo got-int' INT; trap 'echo got-term; exit 9' TERM; echo ready; \
      while :; do sleep 0.05; done")
  | "stop", _ => report (sh "echo ready; kill -STOP $$; echo resumed; exit 4")
  | "exitcode", [n] => IO.print "before-exit"; exitWith (.exited n.toNat!)
  | "exitsig", [n] => IO.print "before-exit"; exitWith (.signaled n.toNat!)
  | _, _ => throw (IO.userError s!"unknown case {name} {rest}")

/-- Run inside `script` (stdin/stdout are a tty). -/
def runPty (pidFile : String) : IO Unit := do
  IO.FS.writeFile pidFile s!"{← IO.Process.getPID}"
  let ids ← ownIds
  let pty (s : ExecSpec) : ExecSpec := { s with usePty := true }
  let sh (script : String) := pty (spec ids "/bin/sh" #["sh", "-c", script])
  IO.println s!"PARENT_TTY {← IO.FS.realPath "/proc/self/fd/0"}"
  -- terminal settings before any pty run (stty in plain mode reads the user's tty)
  IO.print "STTY_BEFORE "
  report (spec ids "/bin/stty" #["stty", "-g"])
  -- input typed at the user's terminal reaches the command through the pty
  report (sh "read x; echo \"got:$x\"")
  report (pty (spec ids "/usr/bin/tty" #["tty"]))
  report (sh "exit 3")
  report (sh "kill -TERM $$")
  report (sh "echo stopping; kill -STOP $$; echo resumed; exit 5")
  report (sh "test -t 1 && echo stdout-is-tty; test -t 0 && echo stdin-is-tty; exit 0")
  IO.print "STTY_AFTER "
  report (spec ids "/bin/stty" #["stty", "-g"])

/-! ## Orchestrator -/

structure Tally where
  pass : Nat := 0
  fail : Nat := 0

def check (t : IO.Ref Tally) (name : String) (ok : Bool) (detail : String) : IO Unit := do
  if ok then
    t.modify fun s => { s with pass := s.pass + 1 }
    IO.println s!"ok   {name}"
  else
    t.modify fun s => { s with fail := s.fail + 1 }
    IO.println s!"FAIL {name}\n----\n{detail}\n----"

def sub (args : Array String) : IO IO.Process.Output := do
  IO.Process.output { cmd := (← IO.appPath).toString, args := #["case"] ++ args }

def lines (s : String) : List String :=
  (s.splitOn "\n").map (fun l => (l.dropEndWhile (· == '\r')).toString)

def has (out : String) (l : String) : Bool := (lines out).contains l

def contains (out needle : String) : Bool := (out.splitOn needle).length > 1

/-- `sh -c script self args…` -/
def shOut (script : String) (args : Array String) (bash := false) : IO IO.Process.Output :=
  IO.Process.output { cmd := if bash then "/bin/bash" else "/bin/sh", args := #["-c", script] ++ args }

def procState (pid : String) : IO Char := do
  try
    let st ← IO.FS.readFile s!"/proc/{pid}/stat"
    -- "pid (comm) S ..." — state follows the last ')'
    match st.splitOn ")" |>.getLast? with
    | some rest => pure (rest.trimAsciiStart.toString.front)
    | none => pure '?'
  catch _ => pure '?'

def waitStopped (pid : String) : IO Bool := do
  for _ in [0:100] do
    if (← procState pid) == 'T' then return true
    IO.sleep 50
  return false

/-- Send `sig` from a helper process that stays alive briefly afterwards: the relay
identifies the sender's process group when the signal arrives, and a sender that has
already been reaped cannot be classified (it is then treated as foreign, like sudo). -/
def kill (sig : String) (pid : String) (newSession := false) : IO Unit := do
  let script := s!"kill {sig} {pid}; sleep 0.3"
  let (cmd, args) := if newSession then ("setsid", #["/bin/sh", "-c", script])
    else ("/bin/sh", #["-c", script])
  discard <| IO.Process.output { cmd, args }

def orchestrate : IO UInt32 := do
  let t ← IO.mkRef ({} : Tally)
  let ids ← ownIds
  let self := (← IO.appPath).toString
  let dir := s!"/tmp/lean-sudo-smoke-exec-{← IO.Process.getPID}"
  IO.FS.createDirAll dir

  -- plain execution
  let o ← sub #["id"]
  check t "id: exit 0 and own uid" (has o.stdout "STATUS exited 0" &&
    contains o.stdout s!"uid={ids.uid}(") o.stdout
  let o ← sub #["exit7"]
  check t "exit code 7" (has o.stdout "STATUS exited 7") o.stdout
  let o ← sub #["term"]
  check t "killed by SIGTERM" (has o.stdout "STATUS signaled 15") o.stdout

  -- exec failures
  let o ← sub #["noent"]
  check t "nonexistent path" (has o.stdout
    "ERROR unable to execute /nonexistent/lean-sudo-smoke: No such file or directory") o.stdout
  let noexec := s!"{dir}/noexec"
  IO.FS.writeFile noexec "#!/bin/sh\necho should-not-run\n"
  discard <| IO.Process.output { cmd := "chmod", args := #["0644", noexec] }
  let o ← sub #["file", noexec]
  check t "non-executable file ⇒ EACCES" (has o.stdout
    s!"ERROR unable to execute {noexec}: Permission denied") o.stdout
  let script := s!"{dir}/script"
  IO.FS.writeFile script "echo \"script-ran $0 $1\"\nexit 3\n"
  discard <| IO.Process.output { cmd := "chmod", args := #["0755", script] }
  let o ← sub #["file", script]
  check t "script without shebang runs via /bin/sh" (has o.stdout s!"script-ran {script} arg1" &&
    has o.stdout "STATUS exited 3") o.stdout

  -- environment, cwd, umask
  let o ← sub #["env"]
  check t "env is exactly the given one" (o.stdout == "FOO=bar\nSPACE=a b\nSTATUS exited 0\n")
    o.stdout
  let o ← sub #["cwd", "/usr"]
  check t "cwd" (o.stdout == "/usr\nSTATUS exited 0\n") o.stdout
  let o ← sub #["cwd", "/nonexistent-dir"]
  check t "bad cwd" (has o.stdout
    "ERROR unable to change directory to /nonexistent-dir: No such file or directory") o.stdout
  let o ← sub #["umask"]
  check t "umask 027" (o.stdout == "0027\nSTATUS exited 0\n") o.stdout
  let o ← sub #["cwdOptional"]
  check t "login cwd failure warns and continues" (has o.stdout "continued" &&
    has o.stdout "STATUS exited 0" && contains o.stderr "unable to change directory") (o.stdout ++ o.stderr)
  let o ← sub #["corelimit"]
  check t "default command core limit is zero" (has o.stdout "0") o.stdout
  let o ← sub #["timeout"]
  check t "timeout kills command" (contains o.stdout "STATUS signaled") o.stdout
  let o ← sub #["missing-noexec"]
  check t "missing noexec library fails closed" (contains o.stdout "ERROR" &&
    !contains o.stdout "must-not-run") o.stdout
  let o ← sub #["badapparmor"]
  check t "AppArmor profile cannot contain NUL" (contains o.stdout "argument contains a NUL byte") o.stdout

  -- closefrom: the wrapper shell opens fd 5 without CLOEXEC
  let cfScript := "exec 5</etc/hostname; exec \"$0\" case closefrom \"$1\""
  let o ← shOut cfScript #[self, "3"]
  let fdLines := (lines o.stdout).filter (fun l => l.all Char.isDigit && !l.isEmpty)
  check t "closefrom 3: only 0-3 (3 = ls's dir fd)" (has o.stdout "PARENT_HAS_5 true" &&
    fdLines.all (fun l => l.toNat! ≤ 3) && has o.stdout "STATUS exited 0") o.stdout
  let o ← shOut cfScript #[self, "6"]
  check t "closefrom 6 keeps fd 5" (has o.stdout "5" && has o.stdout "STATUS exited 0") o.stdout

  -- privilege drop failures (unprivileged): reported, command never runs
  let other := if ids.uid == 0 then 1 else 0
  let m1 := s!"{dir}/marker-uid"
  let o ← sub #["uid", toString other, m1]
  check t "foreign uid ⇒ setresuid error, no exec" (has o.stdout
    s!"ERROR unable to set uid to {other}: Operation not permitted" &&
    !(← System.FilePath.pathExists m1)) o.stdout
  let m2 := s!"{dir}/marker-gid"
  let o ← sub #["gid", toString other, m2]
  check t "foreign gid ⇒ setresgid error, no exec" (has o.stdout
    s!"ERROR unable to set gid to {other}: Operation not permitted" &&
    !(← System.FilePath.pathExists m2)) o.stdout
  let m3 := s!"{dir}/marker-groups"
  let o ← sub #["groups", m3]
  check t "foreign groups ⇒ setgroups error, no exec" (has o.stdout
    "ERROR unable to set supplementary group IDs: Operation not permitted" &&
    !(← System.FilePath.pathExists m3)) o.stdout
  let o ← sub #["baduid"]
  check t "uid (uid_t)-1 rejected" (has o.stdout "ERROR invalid uid 4294967295") o.stdout
  let o ← sub #["nul"]
  check t "NUL in argv rejected" (has o.stdout
    "ERROR unable to execute /bin/sh: argument contains a NUL byte") o.stdout
  let o ← sub #["relpath"]
  check t "relative path rejected" (has o.stdout
    "ERROR unable to execute bin/sh: path is not absolute") o.stdout

  -- background
  let bgf := s!"{dir}/bg"
  -- Capture files rather than pipes: the background supervisor intentionally
  -- retains stdio until the command exits, just like sudo -b.
  let t0 ← IO.monoMsNow
  let o ← shOut "\"$0\" case background \"$1\" >\"$2\" 2>&1" #[self, bgf, s!"{dir}/bg-output"]
  let elapsed := (← IO.monoMsNow) - t0
  check t "background original process exits immediately with 0" (o.exitCode == 0 &&
    elapsed < 400) o.stdout
  IO.sleep 1500
  let bgOut ← try IO.FS.readFile bgf catch _ => pure ""
  check t "background command ran" (bgOut == "bg-done\n") bgOut

  -- signal forwarding
  let child ← IO.Process.spawn {
    cmd := self, args := #["case", "signals"], stdout := .piped, stdin := .null }
  let pid := toString child.pid
  let ready ← child.stdout.getLine
  kill "-INT" pid               -- same process group: must NOT be relayed
  IO.sleep 300
  kill "-INT" pid (newSession := true)  -- other session: relayed
  IO.sleep 300
  kill "-TERM" pid              -- always relayed
  let rest ← child.stdout.readToEnd
  let _ ← child.wait
  let gotInt := ((lines rest).filter (· == "got-int")).length
  check t "signals: INT only from other pgrp, TERM relayed" (ready == "ready\n" &&
    gotInt == 1 && has rest "got-term" && has rest "STATUS exited 9") (ready ++ rest)

  -- child stop ⇒ we stop; SIGCONT ⇒ both resume
  let child ← IO.Process.spawn {
    cmd := self, args := #["case", "stop"], stdout := .piped, stdin := .null }
  let pid := toString child.pid
  let ready ← child.stdout.getLine
  let stopped ← waitStopped pid
  kill "-CONT" pid
  let rest ← child.stdout.readToEnd
  let _ ← child.wait
  check t "stop propagates, continue resumes" (ready == "ready\n" && stopped &&
    has rest "resumed" && has rest "STATUS exited 4") s!"stopped={stopped}\n{ready}{rest}"

  -- exitWith
  let o ← shOut "\"$0\" case exitcode 3; echo \" rc=$?\"" #[self]
  check t "exitWith (.exited 3) flushes and exits 3" (o.stdout == "before-exit rc=3\n") o.stdout
  let o ← shOut "\"$0\" case exitcode 300; echo \" rc=$?\"" #[self]
  check t "exitWith (.exited 300) clamps to 255" (o.stdout == "before-exit rc=255\n") o.stdout
  let o ← shOut "\"$0\" case exitsig 15; echo \" rc=$?\"" #[self] (bash := true)
  check t "exitWith (.signaled 15) re-raises SIGTERM" (o.stdout == "before-exit rc=143\n" &&
    contains o.stderr "Terminated") (o.stdout ++ o.stderr)

  -- pty mode (under script(1) for a controlling terminal)
  let pidFile := s!"{dir}/pty.pid"
  let child ← IO.Process.spawn {
    cmd := "script", args := #["-qec", s!"exec {self} pty {pidFile}", "/dev/null"]
    stdin := .piped, stdout := .piped, stderr := .piped }
  child.stdin.putStr "abc\n"
  child.stdin.flush
  -- wait for the pty case that stops itself, then continue script and us
  let mut ptyStopped := false
  for _ in [0:200] do
    if ← System.FilePath.pathExists pidFile then
      let p := (← IO.FS.readFile pidFile).trimAscii.toString
      if (← procState p) == 'T' then
        ptyStopped := true
        kill "-CONT" (toString child.pid)
        kill "-CONT" p
        break
    IO.sleep 50
  let (_, child) ← child.takeStdin
  let out ← child.stdout.readToEnd
  let _ ← child.wait
  let ls := lines out
  let parentTty := (ls.find? (·.startsWith "PARENT_TTY ")).map (fun l => (l.drop 11).toString)
  let childTty := ls.find? (fun l => l.startsWith "/dev/pts/")
  check t "pty: input relayed" (has out "got:abc") out
  check t "pty: command has its own /dev/pts tty" (match parentTty, childTty with
    | some p, some c => p.startsWith "/dev/pts/" && c != p
    | _, _ => false) out
  check t "pty: exit codes propagate" (has out "STATUS exited 3" &&
    has out "STATUS signaled 15") out
  check t "pty: stop/continue" (ptyStopped && has out "resumed" && has out "STATUS exited 5") out
  check t "pty: tty fds get the pty" (has out "stdout-is-tty" && has out "stdin-is-tty") out
  let stty (k : String) := (ls.find? (·.startsWith k)).map (fun l => (l.drop k.length).toString)
  check t "pty: user terminal settings restored" (match stty "STTY_BEFORE ", stty "STTY_AFTER " with
    | some b, some a => a == b && b.length > 20
    | _, _ => false) out

  -- pty mode with stdout a pipe: stdout passed through as is, stdin gets the pty
  let o ← IO.Process.output {
    cmd := "script", args := #["-qec", s!"{self} case ptypipe | cat", "/dev/null"]
    stdin := .null }
  check t "pty: pipe on stdout is passed through" (contains o.stdout "stdout-is-pipe" &&
    contains o.stdout "stdin-is-tty" && contains o.stdout "STATUS exited 0") o.stdout

  -- pty requested without any tty ⇒ plain mode, no warning
  let o ← IO.Process.output { cmd := self, args := #["case", "exit7pty"], stdin := .null }
  check t "no tty: runs without pty" (has o.stdout "STATUS exited 7" && o.stderr == "") o.stderr

  -- tty fds but no controlling terminal (setsid): pty setup fails ⇒ warning + plain mode
  let o ← IO.Process.output {
    cmd := "script", args := #["-qec", s!"setsid {self} case ptypipe | cat", "/dev/null"]
    stdin := .null }
  check t "pty setup failure falls back with a warning" (contains o.stdout
    "sudo: unable to allocate pty: No such device or address" &&
    contains o.stdout "stdout-is-pipe" && contains o.stdout "STATUS exited 0") o.stdout

  discard <| IO.Process.output { cmd := "rm", args := #["-rf", dir] }
  let s ← t.get
  IO.println s!"smoke-exec: {s.pass} passed, {s.fail} failed"
  pure (if s.fail == 0 then 0 else 1)

end SmokeExec

def main (args : List String) : IO UInt32 := do
  match args with
  | "case" :: name :: rest => SmokeExec.runCase name rest; pure 0
  | ["pty", pidFile] => SmokeExec.runPty pidFile; pure 0
  | [] => SmokeExec.orchestrate
  | _ => IO.eprintln "usage: smoke-exec [case <name> args… | pty <pidfile>]"; pure 2
