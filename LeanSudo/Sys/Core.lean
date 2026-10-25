import LeanSudo.Policy.Types
import LeanSudo.EventLog

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

def S_IFMT : Nat := 0o170000

def FileStat.isReg (s : FileStat) : Bool := (s.mode &&& S_IFMT) == 0o100000
def FileStat.isDir (s : FileStat) : Bool := (s.mode &&& S_IFMT) == 0o040000
def FileStat.isLnk (s : FileStat) : Bool := (s.mode &&& S_IFMT) == 0o120000

private def toId? (n : Nat) : Option UInt32 :=
  if n < UInt32.size then some n.toUInt32 else none

@[extern "lean_sudo_getuid"] opaque getuid : IO Nat
@[extern "lean_sudo_geteuid"] opaque geteuid : IO Nat
@[extern "lean_sudo_set_uid"] opaque setUid (uid : UInt32) : IO Unit
@[extern "lean_sudo_getgid"] opaque getgid : IO Nat
@[extern "lean_sudo_getegid"] opaque getegid : IO Nat

@[extern "lean_sudo_getgroups"] private opaque getgroupsRaw : IO (Array Nat)

def getgroups : IO (List Nat) := return (← getgroupsRaw).toList

@[extern "lean_sudo_getpwnam"] opaque getpwnam (name : @& String) : IO (Option Passwd)

@[extern "lean_sudo_getpwuid"] private opaque getpwuidRaw (uid : UInt32) : IO (Option Passwd)

def getpwuid (uid : Nat) : IO (Option Passwd) :=
  match toId? uid with
  | some u => getpwuidRaw u
  | none => pure none

@[extern "lean_sudo_valid_shells"] opaque validShells : IO (Array String)

@[extern "lean_sudo_getgrnam"] private opaque getgrnamRaw (name : @& String) : IO (Option (String × Nat))
@[extern "lean_sudo_getgrgid"] private opaque getgrgidRaw (gid : UInt32) : IO (Option (String × Nat))

private def toGroupInfo : Option (String × Nat) → Option GroupInfo
  | some (name, gid) => some { name, gid }
  | none => none

def getgrnam (name : String) : IO (Option GroupInfo) :=
  return toGroupInfo (← getgrnamRaw name)

def getgrgid (gid : Nat) : IO (Option GroupInfo) :=
  match toId? gid with
  | some g => return toGroupInfo (← getgrgidRaw g)
  | none => pure none

@[extern "lean_sudo_getgrouplist"] private opaque getgrouplistRaw (user : @& String) (gid : UInt32) : IO (Array Nat)

def getgrouplist (user : String) (gid : Nat) : IO (List Nat) :=
  match toId? gid with
  | some g => return (← getgrouplistRaw user g).toList
  | none => throw (IO.userError "getgrouplist: gid out of range")

@[extern "lean_sudo_gethostname"] opaque gethostname : IO String

@[extern "lean_sudo_isatty"] opaque isatty (fd : UInt32) : IO Bool

@[extern "lean_sudo_ttyname"] opaque ttyname (fd : UInt32) : IO (Option String)

@[extern "lean_sudo_environ"] private opaque environRaw : IO (Array (String × String))

def environ : IO (List (String × String)) := return (← environRaw).toList

@[extern "lean_sudo_stat"] opaque stat (path : @& String) : IO (Option FileStat)

@[extern "lean_sudo_lstat"] opaque lstat (path : @& String) : IO (Option FileStat)

@[extern "lean_sudo_realpath"] opaque realpath (path : @& String) : IO (Option String)

@[extern "lean_sudo_access"] opaque access (path : @& String) (mode : UInt32) : IO Bool

@[extern "lean_sudo_read_file_nofollow"] opaque readFileNoFollow (path : @& String) : IO (FileStat × String)

@[extern "lean_sudo_read_file_follow"] opaque readFileFollow (path : @& String) : IO (FileStat × String)

@[extern "lean_sudo_list_dir"] private opaque listDirRaw (path : @& String) : IO (Array String)

def listDir (path : String) : IO (List String) := return (← listDirRaw path).toList

@[extern "lean_sudo_syslog"] opaque syslog (facility : @& String) (priority : @& String) (msg : @& String) : IO Unit

@[extern "lean_sudo_syslog_bytes"] opaque syslogBytes (facility priority : @& String)
    (msg : @& ByteArray) (pid : Bool) : IO Unit

@[extern "lean_sudo_getcwd"] opaque getcwd : IO String

@[extern "lean_sudo_write_stderr"] opaque writeStderr (s : @& String) : IO Unit

@[extern "lean_sudo_umask"] opaque umask (mask : UInt32) : IO UInt32

@[extern "lean_sudo_unix_time"] opaque unixTime : IO Nat
@[extern "lean_sudo_no_new_privs"] opaque noNewPrivs : IO Bool
@[extern "lean_sudo_terminal_columns"] opaque terminalColumns (fd : UInt32) : IO Nat
@[extern "lean_sudo_local_civil_epoch"]
opaque localCivilEpoch (civil : @& Nat) : IO (Option Int)
@[extern "lean_sudo_architecture"] opaque architecture : IO String

@[extern "lean_sudo_open_command"] opaque openCommand (path : @& String) : IO (Nat × FileStat)
@[extern "lean_sudo_open_readonly"] opaque openReadOnly (path : @& String) : IO (Nat × FileStat)
@[extern "lean_sudo_close_descriptor"] opaque closeDescriptor (fd : UInt32) : IO Unit

@[extern "lean_sudo_admin_flag"] private opaque adminFlagRaw (path : @& String)
    (uid gid : UInt32) (groups : @& Array Nat) : IO Unit

def createAdminFlag (path : String) (uid gid : Nat) (groups : List Nat) : IO Unit := do
  let some u := toId? uid | throw (IO.userError "invalid admin flag uid")
  let some g := toId? gid | throw (IO.userError "invalid admin flag gid")
  adminFlagRaw path u g groups.toArray

@[extern "lean_sudo_log_time"] opaque logTime (year : Bool) (locale : @& String) : IO String
@[extern "lean_sudo_append_log"] opaque appendLog (path text : @& String) : IO Unit
@[extern "lean_sudo_append_json"] opaque appendJson (path member : @& String) : IO Unit
@[extern "lean_sudo_event_time"] opaque eventTime (year : Bool) (locale : @& String) : IO EventLog.Time
@[extern "lean_sudo_event_uuid"] opaque eventUuid : IO String
@[extern "lean_sudo_terminal_size"] opaque terminalSize : IO (Nat × Nat)
@[extern "lean_sudo_signal_name"] opaque signalName (signal : UInt32) : IO String
@[extern "lean_sudo_send_mail"] opaque sendMail (path : @& String)
    (args : @& Array String) (body : @& String) : IO Unit

end LeanSudo.Sys
