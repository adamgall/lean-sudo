import LeanSudo.Policy.Types
import LeanSudo.EventLog
import LeanSudo.Sys.CoreLogs
import LeanSudo.Sys.Prim.CoreFacts
import LeanSudo.Sys.PamHelpers

namespace LeanSudo.Sys

structure Passwd where
  name : String
  uid : Nat
  gid : Nat
  gecos : String
  home : String
  shell : String
  deriving Repr, BEq, Inhabited

structure FileStat where
  dev : Nat
  ino : Nat
  mode : Nat
  uid : Nat
  gid : Nat
  size : Nat
  rdev : Nat
  deriving Repr, BEq, Inhabited

def FileStat.isReg (s : FileStat) : Bool :=
  (s.mode &&& (Prim.Posix.S_IFMT ()).toNat) == (Prim.Posix.S_IFREG ()).toNat
def FileStat.isDir (s : FileStat) : Bool :=
  (s.mode &&& (Prim.Posix.S_IFMT ()).toNat) == (Prim.Posix.S_IFDIR ()).toNat
def FileStat.isLnk (s : FileStat) : Bool :=
  (s.mode &&& (Prim.Posix.S_IFMT ()).toNat) == (Prim.Posix.S_IFLNK ()).toNat

private def toId? (n : Nat) : Option UInt32 :=
  if n < UInt32.size then some n.toUInt32 else none

@[extern "lean_sudo_getuid"] opaque getuid : IO Nat
@[extern "lean_sudo_geteuid"] opaque geteuid : IO Nat
def setUid (uid : UInt32) : IO Unit := do
  Prim.CoreFacts.check (← Prim.CoreFacts.setuid uid)
  let real ← getuid
  let effective ← geteuid
  if real != uid.toNat || effective != uid.toNat then
    Prim.CoreFacts.failErrno (Int.ofNat (Prim.Posix.EPERM ()).toNat)
@[extern "lean_sudo_getgid"] opaque getgid : IO Nat
@[extern "lean_sudo_getegid"] opaque getegid : IO Nat

def getgroups : IO (List Nat) := Prim.CoreFacts.getgroups

private def passwdLookup (call : UInt32 → IO Prim.CoreFacts.NssResult) : IO (Option Passwd) := do
  let some (strings, ids) ← Prim.CoreFacts.lookup false call | return none
  if strings.size != 4 then throw (IO.userError "passwd entry is not valid UTF-8")
  let name ← Prim.CoreFacts.decode strings[0]! "passwd entry is not valid UTF-8"
  let home ← Prim.CoreFacts.decode strings[2]! "passwd entry is not valid UTF-8"
  let shell ← Prim.CoreFacts.decode strings[3]! "passwd entry is not valid UTF-8"
  return some {
    name := name
    uid := ids[0]!
    gid := ids[1]!
    gecos := Prim.CoreFacts.decodeLossy strings[1]!
    home := home
    shell := shell }

def getpwnam (name : String) : IO (Option Passwd) := do
  if name.contains (Char.ofNat 0) then return none
  passwdLookup (Prim.CoreFacts.pwnam name 0)

def getpwuid (uid : Nat) : IO (Option Passwd) :=
  match toId? uid with
  | some u => passwdLookup (Prim.CoreFacts.pwuid "" u)
  | none => pure none

def validShells : IO (Array String) := Prim.CoreFacts.validShells

private def groupLookup (call : UInt32 → IO Prim.CoreFacts.NssResult) : IO (Option GroupInfo) := do
  let some (strings, ids) ← Prim.CoreFacts.lookup true call | return none
  if strings.isEmpty then throw (IO.userError "group entry is not valid UTF-8")
  let name ← Prim.CoreFacts.decode strings[0]! "group entry is not valid UTF-8"
  return some { name, gid := ids[0]! }

def getgrnam (name : String) : IO (Option GroupInfo) := do
  if name.contains (Char.ofNat 0) then return none
  groupLookup (Prim.CoreFacts.grnam name 0)

def getgrgid (gid : Nat) : IO (Option GroupInfo) :=
  match toId? gid with
  | some g => groupLookup (Prim.CoreFacts.grgid "" g)
  | none => pure none

def getgrouplist (user : String) (gid : Nat) : IO (List Nat) :=
  match toId? gid with
  | some g => Prim.CoreFacts.getgrouplist user g
  | none => throw (IO.userError "getgrouplist: gid out of range")

def gethostname : IO String := do
  let (rc, bytes) ← Prim.CoreFacts.hostname
  Prim.CoreFacts.check rc
  Prim.CoreFacts.decode bytes "host name is not valid UTF-8"

@[extern "lean_sudo_isatty"] opaque isatty (fd : UInt32) : IO Bool

def ttyname (fd : UInt32) : IO (Option String) := do
  return (← Prim.CoreFacts.ttyname fd).bind String.fromUTF8?

def environ : IO (List (String × String)) := Prim.CoreFacts.environ

private def fileStat (fields : Array Int) : FileStat :=
  { dev := fields[0]!.toNat
    ino := fields[1]!.toNat
    mode := fields[2]!.toNat
    uid := fields[3]!.toNat
    gid := fields[4]!.toNat
    size := fields[5]!.toNat
    rdev := fields[6]!.toNat }

private def pathStat (path : String) (call : String → IO (Int × Array Int)) :
    IO (Option FileStat) := do
  if path.contains (Char.ofNat 0) then return none
  let (rc, fields) ← call path
  return if rc < 0 then none else some (fileStat fields)

def stat (path : String) : IO (Option FileStat) := pathStat path Prim.CoreFacts.stat

def lstat (path : String) : IO (Option FileStat) := pathStat path Prim.CoreFacts.lstat

def realpath (path : String) : IO (Option String) := do
  if path.contains (Char.ofNat 0) then return none
  return (← Prim.CoreFacts.realpath path).bind String.fromUTF8?

def access (path : String) (mode : UInt32) : IO Bool := do
  if path.contains (Char.ofNat 0) then return false
  return (← Prim.CoreFacts.access path mode) == 0

def readFileNoFollow (path : String) : IO (FileStat × String) := do
  let (fields, text) ← Prim.CoreFacts.readFile path false
  return (fileStat fields, text)

def readFileFollow (path : String) : IO (FileStat × String) := do
  let (fields, text) ← Prim.CoreFacts.readFile path true
  return (fileStat fields, text)

def listDir (path : String) : IO (List String) := Prim.CoreFacts.listDir path

def syslog (facility priority msg : String) : IO Unit := CoreLogs.syslog facility priority msg

def syslogBytes (facility priority : String) (msg : ByteArray) (pid : Bool) : IO Unit :=
  CoreLogs.syslogBytes facility priority msg pid

def getcwd : IO String := do
  let (rc, bytes) ← Prim.CoreFacts.getcwd
  Prim.CoreFacts.check rc
  Prim.CoreFacts.decode bytes "current directory is not valid UTF-8"

def currentDirectory : IO (Option String) := do
  let (rc, bytes) ← Prim.CoreFacts.getcwd
  if rc < 0 then return none
  some <$> Prim.CoreFacts.decode bytes "current directory is not valid UTF-8"

def writeStderr (s : String) : IO Unit := Prim.CoreFacts.writeStderr s.toUTF8

@[extern "lean_sudo_umask"] private opaque umaskRaw (mask : UInt32) : IO UInt32

def umask (mask : UInt32) : IO UInt32 :=
  umaskRaw (mask &&& (Prim.Posix.S_ISUID () ||| Prim.Posix.S_ISGID () ||| Prim.Posix.S_ISVTX () |||
    Prim.Posix.S_IRWXU () ||| Prim.Posix.S_IRWXG () ||| Prim.Posix.S_IRWXO ()))

def unixTime : IO Nat := CoreLogs.unixTime
def noNewPrivs : IO Bool := CoreLogs.noNewPrivs
def terminalColumns (fd : UInt32) : IO Nat := CoreLogs.terminalColumns fd
def localCivilEpoch (civil : Nat) : IO (Option Int) := CoreLogs.localCivilEpoch civil
def architecture : IO String := CoreLogs.architecture

def openCommand (path : String) : IO (Nat × FileStat) := do
  let (fd, fields) ← Prim.CoreFacts.openReadOnly path true
  return (fd, fileStat fields)

def openReadOnly (path : String) : IO (Nat × FileStat) := do
  let (fd, fields) ← Prim.CoreFacts.openReadOnly path false
  return (fd, fileStat fields)

def closeDescriptor (fd : UInt32) : IO Unit := Prim.CoreFacts.closeDescriptor fd


def createAdminFlag (path : String) (uid gid : Nat) (groups : List Nat) : IO Unit := do
  let some u := toId? uid | throw (IO.userError "invalid admin flag uid")
  let some g := toId? gid | throw (IO.userError "invalid admin flag gid")
  if path.contains '\x00' then throw (IO.userError "invalid admin flag arguments")
  if groups.any (· ≥ UInt32.size - 1) then throw (IO.userError "invalid admin flag group")
  PamHelpers.createAdminFlag path u g (groups.toArray.map Nat.toUInt32)

def logTime (year : Bool) (locale : String) : IO String := CoreLogs.logTime year locale
def appendLog (path text : String) : IO Unit := CoreLogs.appendLog path text
def appendJson (path member : String) : IO Unit := CoreLogs.appendJson path member
def eventTime (year : Bool) (locale : String) : IO EventLog.Time := CoreLogs.eventTime year locale
def eventUuid : IO String := CoreLogs.eventUuid
def terminalSize : IO (Nat × Nat) := CoreLogs.terminalSize
def signalName (signal : UInt32) : IO String := CoreLogs.signalName signal
def sendMail (path : String) (args : Array String) (body : String) : IO Unit :=
  PamHelpers.sendMail path args body

end LeanSudo.Sys
