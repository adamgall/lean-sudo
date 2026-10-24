import LeanSudo.Policy.Types
import LeanSudo.EventLog

/-!
# `LeanSudo.Sys.Core` — thin FFI bindings to `c/core.c`

Users/groups/host/tty/stat/realpath/secure read/environ/syslog. No policy lives here.

Conventions:
* Errors are `IO.userError`s carrying `strerror` text (possibly prefixed with context
  such as `unable to open <path>: `) unless the function returns an `Option`.
* String arguments containing a NUL byte are rejected (`none`/`false`/error) instead of
  being truncated by C.
* Strings coming from C are validated as UTF-8; how invalid data is handled is
  documented per function.
* Numeric ids are `Nat`; ids that do not fit in a 32-bit `uid_t`/`gid_t` are never found.
-/

namespace LeanSudo.Sys

/-- A passwd entry. The C side constructs this structure directly (6 boxed fields, in
this order) — do not reorder the fields. -/
structure Passwd where
  name : String
  uid : Nat
  gid : Nat
  gecos : String
  home : String
  shell : String
  deriving Repr, BEq, Inhabited

/-- Result of `stat(2)`. The C side constructs this structure directly (7 boxed `Nat`
fields, in this order) — do not reorder the fields. -/
structure FileStat where
  dev : Nat
  ino : Nat
  /-- full `st_mode` including the file type bits -/
  mode : Nat
  uid : Nat
  gid : Nat
  size : Nat
  rdev : Nat
  deriving Repr, BEq, Inhabited

/-- `S_IFMT` -/
def S_IFMT : Nat := 0o170000

def FileStat.isReg (s : FileStat) : Bool := (s.mode &&& S_IFMT) == 0o100000
def FileStat.isDir (s : FileStat) : Bool := (s.mode &&& S_IFMT) == 0o040000
def FileStat.isLnk (s : FileStat) : Bool := (s.mode &&& S_IFMT) == 0o120000

/-- Converts a `Nat` id to the C width, `none` if it does not fit. -/
private def toId? (n : Nat) : Option UInt32 :=
  if n < UInt32.size then some n.toUInt32 else none

@[extern "lean_sudo_getuid"] opaque getuid : IO Nat
@[extern "lean_sudo_geteuid"] opaque geteuid : IO Nat
@[extern "lean_sudo_getgid"] opaque getgid : IO Nat
@[extern "lean_sudo_getegid"] opaque getegid : IO Nat

@[extern "lean_sudo_getgroups"] private opaque getgroupsRaw : IO (Array Nat)

/-- Supplementary groups of this process (`getgroups(2)`). -/
def getgroups : IO (List Nat) := return (← getgroupsRaw).toList

/-- `getpwnam_r`; `none` if there is no such user. Errors if the entry's name, home or
shell is not valid UTF-8 (the gecos field is decoded lossily). -/
@[extern "lean_sudo_getpwnam"] opaque getpwnam (name : @& String) : IO (Option Passwd)

@[extern "lean_sudo_getpwuid"] private opaque getpwuidRaw (uid : UInt32) : IO (Option Passwd)

/-- `getpwuid_r`; `none` if there is no such user. -/
def getpwuid (uid : Nat) : IO (Option Passwd) :=
  match toId? uid with
  | some u => getpwuidRaw u
  | none => pure none

/-- libc's getusershell list, including its missing-file fallback and token rules. -/
@[extern "lean_sudo_valid_shells"] opaque validShells : IO (Array String)

@[extern "lean_sudo_getgrnam"] private opaque getgrnamRaw (name : @& String) : IO (Option (String × Nat))
@[extern "lean_sudo_getgrgid"] private opaque getgrgidRaw (gid : UInt32) : IO (Option (String × Nat))

private def toGroupInfo : Option (String × Nat) → Option GroupInfo
  | some (name, gid) => some { name, gid }
  | none => none

/-- `getgrnam_r`; `none` if there is no such group. Errors if the name is not UTF-8. -/
def getgrnam (name : String) : IO (Option GroupInfo) :=
  return toGroupInfo (← getgrnamRaw name)

/-- `getgrgid_r`; `none` if there is no such group. Errors if the name is not UTF-8. -/
def getgrgid (gid : Nat) : IO (Option GroupInfo) :=
  match toId? gid with
  | some g => return toGroupInfo (← getgrgidRaw g)
  | none => pure none

@[extern "lean_sudo_getgrouplist"] private opaque getgrouplistRaw (user : @& String) (gid : UInt32) : IO (Array Nat)

/-- `getgrouplist(3)` (growing buffer): all groups `user` is a member of, including `gid`. -/
def getgrouplist (user : String) (gid : Nat) : IO (List Nat) :=
  match toId? gid with
  | some g => return (← getgrouplistRaw user g).toList
  | none => throw (IO.userError "getgrouplist: gid out of range")

/-- `gethostname(2)` (the full, unshortened name). -/
@[extern "lean_sudo_gethostname"] opaque gethostname : IO String

@[extern "lean_sudo_isatty"] opaque isatty (fd : UInt32) : IO Bool

/-- `ttyname_r`; `none` if `fd` is not a terminal (or the name is not UTF-8). -/
@[extern "lean_sudo_ttyname"] opaque ttyname (fd : UInt32) : IO (Option String)

@[extern "lean_sudo_environ"] private opaque environRaw : IO (Array (String × String))

/-- The process environment as `(name, value)` pairs, split at the first `=`, in
`environ` order. Entries that are not valid UTF-8 or lack `=` are dropped. -/
def environ : IO (List (String × String)) := return (← environRaw).toList

/-- `stat(2)`; `none` on any failure. -/
@[extern "lean_sudo_stat"] opaque stat (path : @& String) : IO (Option FileStat)

/-- `lstat(2)`; `none` on any failure. -/
@[extern "lean_sudo_lstat"] opaque lstat (path : @& String) : IO (Option FileStat)

/-- `realpath(3)`; `none` on any failure (or if the result is not valid UTF-8). -/
@[extern "lean_sudo_realpath"] opaque realpath (path : @& String) : IO (Option String)

/-- `access(2)` (checks with the *real* uid/gid). `mode` is `F_OK`=0, `X_OK`=1,
`W_OK`=2, `R_OK`=4 or a combination. -/
@[extern "lean_sudo_access"] opaque access (path : @& String) (mode : UInt32) : IO Bool

/-- open with O_RDONLY|O_NOFOLLOW|O_CLOEXEC, fstat the *opened* fd, read it fully.

Also uses `O_NONBLOCK` (so a FIFO cannot block the open) and `O_NOCTTY`. Errors:
`unable to open <path>: <strerror>` (a symlink yields ELOOP), `<path> is not a regular
file`, `<path>: file too large` (cap 16 MiB), `unable to read <path>: <strerror>`,
`<path>: file is not valid UTF-8`. -/
@[extern "lean_sudo_read_file_nofollow"] opaque readFileNoFollow (path : @& String) : IO (FileStat × String)

/-- Follow symlinks, then inspect and read the opened regular file. -/
@[extern "lean_sudo_read_file_follow"] opaque readFileFollow (path : @& String) : IO (FileStat × String)

@[extern "lean_sudo_list_dir"] private opaque listDirRaw (path : @& String) : IO (Array String)

/-- Entry names of a directory, excluding `.` and `..`, in `readdir` order (unsorted).
Errors (fail-closed) if an entry name is not valid UTF-8. -/
def listDir (path : String) : IO (List String) := return (← listDirRaw path).toList

/-- `openlog("sudo", LOG_PID, facility); syslog(facility|priority, "%s", msg); closelog()`.
Facilities: `authpriv auth daemon user local0`…`local7`; priorities:
`alert crit err warning notice info debug`. Unknown names are errors. -/
@[extern "lean_sudo_syslog"] opaque syslog (facility : @& String) (priority : @& String) (msg : @& String) : IO Unit

@[extern "lean_sudo_syslog_bytes"] opaque syslogBytes (facility priority : @& String)
    (msg : @& ByteArray) (pid : Bool) : IO Unit

@[extern "lean_sudo_getcwd"] opaque getcwd : IO String

/-- Unbuffered write of the whole string to fd 2. -/
@[extern "lean_sudo_write_stderr"] opaque writeStderr (s : @& String) : IO Unit

/-- `umask(2)`: sets the file mode creation mask to `mask &&& 0o7777` and returns the
previous mask. -/
@[extern "lean_sudo_umask"] opaque umask (mask : UInt32) : IO UInt32

@[extern "lean_sudo_unix_time"] opaque unixTime : IO Nat
@[extern "lean_sudo_no_new_privs"] opaque noNewPrivs : IO Bool
@[extern "lean_sudo_terminal_columns"] opaque terminalColumns (fd : UInt32) : IO Nat
@[extern "lean_sudo_utc_offset"] opaque utcOffset : IO Int
@[extern "lean_sudo_architecture"] opaque architecture : IO String

/-- Pin the executable and inspect that descriptor, not a second pathname lookup. -/
@[extern "lean_sudo_open_command"] opaque openCommand (path : @& String) : IO (Nat × FileStat)
/-- Open nonblocking, following symlinks, and return the opened descriptor's fstat.
The caller checks ownership/type/mode before reading any bytes. -/
@[extern "lean_sudo_open_readonly"] opaque openReadOnly (path : @& String) : IO (Nat × FileStat)
@[extern "lean_sudo_close_descriptor"] opaque closeDescriptor (fd : UInt32) : IO Unit

@[extern "lean_sudo_admin_flag"] private opaque adminFlagRaw (path : @& String)
    (uid gid : UInt32) (groups : @& Array Nat) : IO Unit

def createAdminFlag (path : String) (uid gid : Nat) (groups : List Nat) : IO Unit := do
  let some u := toId? uid | throw (IO.userError "invalid admin flag uid")
  let some g := toId? gid | throw (IO.userError "invalid admin flag gid")
  adminFlagRaw path u g groups.toArray

@[extern "lean_sudo_log_time"] opaque logTime (year : Bool) : IO String
@[extern "lean_sudo_append_log"] opaque appendLog (path text : @& String) : IO Unit
/-- Locked seek-and-append for sudo's pretty JSON object, not JSON lines. -/
@[extern "lean_sudo_append_json"] opaque appendJson (path member : @& String) : IO Unit
@[extern "lean_sudo_event_time"] opaque eventTime (year : Bool) : IO EventLog.Time
@[extern "lean_sudo_event_uuid"] opaque eventUuid : IO String
@[extern "lean_sudo_terminal_size"] opaque terminalSize : IO (Nat × Nat)
@[extern "lean_sudo_signal_name"] opaque signalName (signal : UInt32) : IO String
@[extern "lean_sudo_send_mail"] opaque sendMail (path : @& String)
    (args : @& Array String) (body : @& String) : IO Unit

end LeanSudo.Sys
