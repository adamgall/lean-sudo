import LeanSudo.Sys.Core
import LeanSudo.Sys.Prim.Plugins
import LeanSudo.Sys.Prim.Posix
import LeanSudo.Background
import LeanSudo.Sys.Limits

namespace LeanSudo.Sys.Plugins

private def dimension (text : Option String) (fallback : Nat) : Nat :=
  match text.bind String.toNat? with
  | some n => if n > 0 && n <= (Prim.Posix.INT_MAX ()).toNat then n else fallback
  | none => fallback

private def octalMask (n : Nat) : String :=
  "0" ++ (if n >= 64 then toString (n / 64 % 8) else "") ++
    (if n >= 8 then toString (n / 8 % 8) else "") ++ toString (n % 8)

private def terminalName (tty : UInt32) : IO (Option Nat × Option String) := do
  let mut device := (← Prim.Plugins.ttydev tty).map UInt32.toNat
  let mut name := none
  for fd in [Prim.Posix.STDIN_FILENO (), Prim.Posix.STDOUT_FILENO (),
      Prim.Posix.STDERR_FILENO ()] do
    let some path ← ttyname fd | continue
    let some st ← stat s!"/proc/self/fd/{fd}" | continue
    if device.isNone || device == some st.rdev then
      device := some st.rdev
      name := some path
      break
  if name.isNone && Prim.Plugins.linuxDevices () then
    if let some dev := device then
      let major := (Prim.Plugins.deviceMajor dev.toUInt64).toNat
      let minor := (Prim.Plugins.deviceMinor dev.toUInt64).toNat
      let ptyBase := (Prim.Plugins.ptySlaveMajor ()).toNat
      let ptyCount := (Prim.Plugins.ptyMajorCount ()).toNat
      let serialBase := (Prim.Plugins.ttySerialBase ()).toNat
      let path := if major >= ptyBase && major < ptyBase + ptyCount then
          let index := (major - ptyBase) * (Prim.Plugins.ptyMinorCount ()).toNat + minor
          some s!"/dev/pts/{index}"
        else if major == (Prim.Plugins.ttyMajor ()).toNat then
          some (if minor < serialBase then s!"/dev/tty{minor}"
            else s!"/dev/ttyS{minor - serialBase}")
        else none
      if let some path := path then
        if let some st ← stat path then
          if st.rdev == dev then name := some path
  return (device, name)

def userInfo (groupSource : String) (maxGroups : UInt32) : IO (Array String) := do
  let uid ← getuid
  let some pw ← getpwuid uid | throw (IO.userError "you do not exist in the passwd database")
  let tty ← Prim.Plugins.openTty
    (Prim.Posix.O_RDWR () ||| Prim.Posix.O_NOCTTY () ||| Prim.Posix.O_CLOEXEC ())
  try
    let tcpgid ← if tty == 0xffffffff then pure 0 else Prim.Plugins.tcgetpgrp tty
    let sid ← Prim.Plugins.getsid
    let (rows, cols) ← Prim.Plugins.winsize tty
    let validSize := rows != 0 && cols != 0
    let rows ← if validSize then pure rows.toNat
      else pure <| dimension (← IO.getEnv "LINES") 24
    let cols ← if validSize then pure cols.toNat
      else pure <| dimension (← IO.getEnv "COLUMNS") 80
    let gid ← getgid
    let (pid, ppid) ← match ← Background.invokingProcess with
      | some ids => pure ids
      | none => do
        let pid ← Prim.Plugins.getpid
        let ppid ← Prim.Plugins.getppid
        pure (pid.toNat, ppid.toNat)
    let mut info := #[s!"user={pw.name}", s!"pid={pid}",
      s!"ppid={ppid}", s!"pgid={← Prim.Plugins.getpgrp}",
      s!"tcpgid={if tcpgid == 0xffffffff then 0 else tcpgid}",
      s!"sid={if sid == 0xffffffff then 0 else sid}", s!"uid={uid}", s!"euid={← geteuid}",
      s!"gid={gid}", s!"egid={← getegid}"]
    let kernelLimit ← Prim.Plugins.groupMax
    let kernelMax := if kernelLimit == 0 - 1 then (Prim.Plugins.groupsFallback ()).toNat
      else kernelLimit.toNat
    let staticGroups ← if groupSource == "dynamic" then pure [] else getgroups
    let groups ← if !staticGroups.isEmpty &&
        (staticGroups.length != kernelMax || groupSource == "static") then pure staticGroups
      else do
        if maxGroups > Prim.Posix.INT_MAX () then
          throw (IO.userError "unable to collect plugin user information")
        let groups ← getgrouplist pw.name gid
        pure <| if maxGroups == 0 then groups else groups.take maxGroups.toNat
    info := info.push ("groups=" ++ String.intercalate "," (groups.map toString))
    let mask ← umask 0
    discard <| umask mask
    info := info.push ("umask=" ++ octalMask mask.toNat)
    try info := info.push ("cwd=" ++ (← getcwd)) catch _ => pure ()
    let (dev, name) ← terminalName tty
    if let some dev := dev then info := info.push s!"ttydev={dev}"
    if let some name := name then info := info.push ("tty=" ++ name)
    let host ← try gethostname catch _ => pure "localhost"
    info := info ++ #["host=" ++ host, s!"lines={rows}", s!"cols={cols}"]
    for (name, index) in (#["as", "core", "cpu", "data", "fsize", "locks", "memlock",
        "nofile", "nproc", "rss", "stack"] : Array String).zipIdx do
      if let some (soft, hard) ← Limits.original (Prim.Plugins.limitResource index) then
        let format := fun (n : UInt64) =>
          if n == Prim.Plugins.limitInfinity () then "infinity" else toString n
        info := info.push s!"rlimit_{name}={format soft},{format hard}"
    return info
  finally
    if tty != 0xffffffff then discard <| Prim.Plugins.closeFd tty

end LeanSudo.Sys.Plugins
