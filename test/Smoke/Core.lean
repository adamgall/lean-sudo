import LeanSudo.Sys.Core
import LeanSudo.Sys.Pam

/-!
Smoke test for `LeanSudo.Sys.Core` / `LeanSudo.Sys.Pam` (runs unprivileged).

`smoke-core` runs everything; it re-invokes itself as
* `smoke-core stdin-auth` with a wrong password piped to stdin (`-S` path),
* `smoke-core stdin-auth` with empty stdin,
* `setsid -w smoke-core tty-auth` (no controlling terminal ⇒ "a terminal is required").
`smoke-core tty-auth [feedback]` can also be run by hand on a terminal (prompt `pw: `;
with `feedback`, pwfeedback is on).
Exit code is non-zero if any check fails.
-/

open LeanSudo LeanSudo.Sys

def check (failures : IO.Ref Nat) (name : String) (ok : Bool) (detail : String := "") : IO Unit := do
  IO.println s!"[{if ok then "ok" else "FAIL"}] {name}{if detail.isEmpty then "" else ": " ++ detail}"
  unless ok do failures.modify (· + 1)

def showStat : Option FileStat → String
  | some s => s!"mode={String.ofList (Nat.toDigits 8 s.mode)} uid={s.uid} gid={s.gid} size={s.size} reg={s.isReg} dir={s.isDir} lnk={s.isLnk}"
  | none => "none"

def me : IO String := do
  match ← getpwuid (← getuid) with
  | some pw => pure pw.name
  | none => throw (IO.userError "no passwd entry for self")

/-- `-S` path: read the password from stdin. Exit 0 iff authentication failed cleanly. -/
def stdinAuth (service : String) (timeout : Nat := 0) : IO UInt32 := do
  let user ← me
  let h ← pamStart service user
    { useStdin := true, prompt := s!"[sudo] password for {user}: ", timeout } user none
  let rc ← pamAuthenticate h
  let msg ← pamStrerror h rc
  let conv ← pamLastConvError h
  pamEnd h rc
  IO.println s!"stdin-auth: rc={rc} ({msg}) convError={conv}"
  return if rc != 0 then 0 else 1

/-- `/dev/tty` path. Without a controlling terminal exit 0 iff the tty error is reported;
with one (manual/pty testing) it prompts `pw: ` and reports the result. -/
def ttyAuth (pwfeedback : Bool) : IO UInt32 := do
  let user ← me
  let h ← pamStart "sudo" user { prompt := "pw: ", pwfeedback } user none
  let rc ← pamAuthenticate h
  let conv ← pamLastConvError h
  pamEnd h rc
  IO.println s!"tty-auth: rc={rc} convError={conv}"
  return if rc != 0 && (conv.getD "").startsWith "a terminal is required" then 0 else 1

/-- Runs this executable with `args`, writes `input` to its stdin and closes it (or, with
`keepOpen`, keeps stdin open until the child exited). -/
def runChild (args : Array String) (input : String) (cmd : Option String := none)
    (keepOpen := false) : IO (UInt32 × String × String) := do
  let self ← IO.appPath
  let (cmd, args) := match cmd with
    | some c => (c, #["-w", self.toString] ++ args)
    | none => (self.toString, args)
  let child ← IO.Process.spawn
    { cmd, args, stdin := .piped, stdout := .piped, stderr := .piped }
  let (stdin, child) ← child.takeStdin
  stdin.putStr input
  stdin.flush
  let keep := if keepOpen then some stdin else none -- otherwise dropped here ⇒ closed
  let out ← IO.asTask child.stdout.readToEnd
  let err ← child.stderr.readToEnd
  let rc ← child.wait
  let out ← IO.ofExcept out.get
  if let some h := keep then h.flush
  return (rc, out, err)

def all : IO UInt32 := do
  let failures ← IO.mkRef 0
  let uid ← getuid; let euid ← geteuid; let gid ← getgid; let egid ← getegid
  IO.println s!"uid={uid} euid={euid} gid={gid} egid={egid}"
  let root ← getpwnam "root"
  IO.println s!"getpwnam root = {repr root}"
  check failures "getpwnam root" (root.map (·.uid) == some 0)
  check failures "getpwnam nonexistent" ((← getpwnam "no-such-user-xyz").isNone)
  check failures "getpwnam with NUL" ((← getpwnam "root\x00x").isNone)
  let self ← getpwuid uid
  IO.println s!"getpwuid self = {repr self}"
  check failures "getpwuid self" (self.map (·.uid) == some uid)
  check failures "getpwuid out of range" ((← getpwuid (2^40)).isNone)
  let gr0 ← getgrgid 0
  IO.println s!"getgrgid 0 = {repr gr0}"
  check failures "getgrgid 0" (gr0.map (·.name) == some "root")
  check failures "getgrnam root" ((← getgrnam "root").map (·.gid) == some 0)
  let groups ← getgroups
  IO.println s!"getgroups = {groups}"
  let name := (self.map (·.name)).getD "root"
  let gl ← getgrouplist name gid
  IO.println s!"getgrouplist {name} {gid} = {gl}"
  check failures "getgrouplist contains primary gid" (gl.contains gid)
  let host ← gethostname
  IO.println s!"gethostname = {host}"
  check failures "gethostname nonempty" (!host.isEmpty)
  for fd in [0, 1, 2] do
    IO.println s!"fd {fd}: isatty={← isatty fd} ttyname={← ttyname fd}"
  let env ← environ
  IO.println s!"environ: {env.length} entries; first 3: {env.take 3}"
  check failures "environ has PATH" (env.any (·.1 == "PATH"))
  let cwd ← getcwd
  IO.println s!"getcwd = {cwd}"
  IO.println s!"stat /etc/sudoers = {showStat (← stat "/etc/sudoers")}"
  IO.println s!"lstat /etc/sudoers = {showStat (← lstat "/etc/sudoers")}"
  -- a symlink we create ourselves
  let tmp := "/tmp/lean-sudo-smoke-core"
  IO.FS.createDirAll tmp
  let regular := tmp ++ "/regular"
  let link := tmp ++ "/link"
  IO.FS.writeFile regular "hello\nwörld\n"
  if (← lstat link).isSome then IO.FS.removeFile link
  let ln ← IO.Process.output { cmd := "ln", args := #["-s", regular, link] }
  check failures "create symlink" (ln.exitCode == 0)
  let ls ← lstat link
  let st ← stat link
  IO.println s!"lstat link = {showStat ls}"
  IO.println s!"stat link = {showStat st}"
  check failures "lstat symlink isLnk" ((ls.map (·.isLnk)) == some true)
  check failures "stat symlink isReg" ((st.map (·.isReg)) == some true)
  check failures "stat /etc isDir" (((← stat "/etc").map (·.isDir)) == some true)
  check failures "stat missing" ((← stat "/nonexistent/x").isNone)
  let rp ← realpath "/bin/ls"
  IO.println s!"realpath /bin/ls = {rp}"
  check failures "realpath /bin/ls" (rp.isSome)
  check failures "realpath link" ((← realpath link) == some regular)
  check failures "access /bin/ls X_OK" (← access "/bin/ls" 1)
  check failures "access /etc/shadow R_OK false" (!(← access "/etc/shadow" 4) || uid == 0)
  let (fst, contents) ← readFileNoFollow regular
  check failures "readFileNoFollow regular" (contents == "hello\nwörld\n" && fst.isReg && fst.size == 13)
    s!"{repr contents} {showStat (some fst)}"
  for (p, why) in [(link, "symlink"), ("/etc", "directory"), ("/dev/null", "char device"),
      ("/nonexistent/x", "missing")] do
    try
      let _ ← readFileNoFollow p
      check failures s!"readFileNoFollow {why} must fail" false
    catch e =>
      check failures s!"readFileNoFollow {why} fails" true (toString e)
  IO.FS.writeFile (tmp ++ "/bad") ""
  let h ← IO.FS.Handle.mk (tmp ++ "/bad") .write
  h.write (ByteArray.mk #[0xff, 0xfe])
  h.flush
  try
    let _ ← readFileNoFollow (tmp ++ "/bad")
    check failures "readFileNoFollow invalid UTF-8 must fail" false
  catch e =>
    check failures "readFileNoFollow invalid UTF-8 fails" true (toString e)
  try
    let d ← listDir "/etc/sudoers.d"
    IO.println s!"listDir /etc/sudoers.d = {d}"
  catch e => IO.println s!"listDir /etc/sudoers.d: {e}"
  let d ← listDir tmp
  check failures "listDir tmp" (d.contains "regular" && d.contains "link" && !d.contains ".")
    s!"{d}"
  syslog "user" "info" s!"lean-sudo smoke-core test message (uid {uid})"
  check failures "syslog user/info" true
  try
    syslog "bogus" "info" "x"
    check failures "syslog bogus facility must fail" false
  catch e => check failures "syslog bogus facility fails" true (toString e)
  writeStderr "writeStderr: hello from smoke-core\n"
  let old ← umask 0o077
  let mid ← umask old
  let back ← umask old
  IO.println s!"umask: previous={String.ofList (Nat.toDigits 8 old.toNat)}"
  check failures "umask set/restore" (mid == 0o077 && back == old)
  -- PAM
  let avail ← pamAvailable
  check failures "pamAvailable" avail
  if avail then
    let h ← pamStart "sudo" name { nonInteractive := true, prompt := "pw: " } name (← ttyname 0)
    let rc ← pamAuthenticate h
    let msg ← pamStrerror h rc
    let conv ← pamLastConvError h
    IO.println s!"non-interactive pamAuthenticate = {rc} ({msg}); convError={conv}"
    check failures "non-interactive auth fails" (rc != 0)
    check failures "non-interactive conv error" (conv == some "a password is required")
    IO.println s!"pamGetEnv = {← pamGetEnv h}"
    let su ← pamSetUser h "root"
    check failures "pamSetUser root" (su == 0) s!"{su}"
    pamEnd h rc
    pamEnd h rc
    try
      let _ ← pamAuthenticate h
      check failures "use after pamEnd must fail" false
    catch e => check failures "use after pamEnd fails" true (toString e)
    -- handle dropped without pamEnd: finalizer must call pam_end
    let h2 ← pamStart "sudo" name {} name none
    IO.println s!"pamStrerror 7 = {← pamStrerror h2 7}"
    try
      let _ ← pamStart "sudo" "root\x00" {} name none
      check failures "pamStart with NUL must fail" false
    catch e => check failures "pamStart with NUL fails" true (toString e)
    -- -S with a wrong password
    let (rc, out, err) ← runChild #["stdin-auth"] "definitely-wrong-password\n"
    IO.println s!"child stdin-auth (wrong pw): exit={rc}\n  stdout: {out.trimAscii}\n  stderr: {repr err}"
    check failures "-S wrong password fails cleanly" (rc == 0 && out.contains "rc=7")
    check failures "-S prompt on stderr" ((err.splitOn "[sudo] password for").length > 1)
    let (rc, out, _) ← runChild #["stdin-auth"] ""
    IO.println s!"child stdin-auth (empty stdin): exit={rc} stdout: {out.trimAscii}"
    check failures "-S empty stdin fails" (rc == 0 && out.contains "no password was provided")
    let (rc, out, _) ← runChild #["stdin-auth-timeout"] "" (keepOpen := true)
    IO.println s!"child stdin-auth (1s timeout, open stdin): exit={rc} stdout: {out.trimAscii}"
    check failures "-S timeout" (rc == 0 && out.contains "timed out reading password")
    if (← access "/usr/bin/setsid" 1) then
      let (rc, out, err) ← runChild #["tty-auth"] "" (cmd := some "/usr/bin/setsid")
      IO.println s!"child tty-auth (no ctty): exit={rc} stdout: {out.trimAscii} stderr: {repr err}"
      check failures "no tty ⇒ terminal required error" (rc == 0)
  let n ← failures.get
  IO.println s!"{n} failure(s)"
  return if n == 0 then 0 else 1

def main (args : List String) : IO UInt32 := do
  match args with
  | ["stdin-auth"] => stdinAuth "sudo"
  | ["stdin-auth-timeout"] => stdinAuth "sudo" (timeout := 1)
  | ["tty-auth"] => ttyAuth false
  | ["tty-auth", "feedback"] => ttyAuth true
  | [] => all
  | _ => IO.eprintln "usage: smoke-core [stdin-auth | tty-auth [feedback]]"; return 2
