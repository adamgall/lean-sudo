import LeanSudo.Intercept.Registers
import LeanSudo.Sys.Prim.Posix
import LeanSudo.Sys.Prim.CoreFacts

namespace LeanSudo.Sys.Prim.Intercept

@[extern "lean_intercept_constants"]
private opaque constantRaw (index : UInt32) : UInt64

private def n (index : UInt32) : Nat := (constantRaw index).toNat
private def u (index : UInt32) : UInt32 := (constantRaw index).toUInt32

def wordBytes (_ : Unit) : Nat := n 0
def pointerBytes (_ : Unit) : Nat := n 1
def loopback (_ : Unit) : UInt32 := u 3
def intBytes (_ : Unit) : Nat := n 2
def inet (_ : Unit) : UInt32 := u 4
def stream (_ : Unit) : UInt32 := u 5
def tcp (_ : Unit) : UInt32 := u 6
def noDelay (_ : Unit) : UInt32 := u 7
def pollIn (_ : Unit) : UInt32 := u 8
def pollOut (_ : Unit) : UInt32 := u 9
def pollError (_ : Unit) : UInt32 := u 10
def pollInvalid (_ : Unit) : UInt32 := u 11
def pollHangup (_ : Unit) : UInt32 := u 12
def setidBits (_ : Unit) : Nat := n 13
def noSyscall (_ : Unit) : Nat := n 14
def accessDenied (_ : Unit) : Nat := n 15
def noChild (_ : Unit) : Int64 := (n 16).toInt64
def trapSignal (_ : Unit) : UInt32 := u 17
def addressSize (_ : Unit) : Nat := n 18
def familyOffset (_ : Unit) : Nat := n 19
def familyWidth (_ : Unit) : Nat := n 20
def portOffset (_ : Unit) : Nat := n 21
def portWidth (_ : Unit) : Nat := n 22
def addressOffset (_ : Unit) : Nat := n 23
def addressWidth (_ : Unit) : Nat := n 24
def stopMask (_ : Unit) : UInt32 := u 26
def signalMask (_ : Unit) : UInt32 := u 27
def stoppedValue (_ : Unit) : UInt32 := u 28
def signalShift (_ : Unit) : UInt32 := u 29
def eventShift (_ : Unit) : UInt32 := u 30
def syscallTrap (_ : Unit) : UInt32 := u 31
def registerNote (_ : Unit) : UInt32 := u 32
def armSyscallNote (_ : Unit) : UInt32 := u 33
def peek (_ : Unit) : UInt32 := u 34
def poke (_ : Unit) : UInt32 := u 35
def stepSyscall (_ : Unit) : UInt32 := u 36
def resume (_ : Unit) : UInt32 := u 37
def seize (_ : Unit) : UInt32 := u 38
def traceOptions (_ : Unit) : UInt64 := constantRaw 39
def traceListen (_ : Unit) : UInt32 := u 40
def detach (_ : Unit) : UInt32 := u 41
def interrupt (_ : Unit) : UInt32 := u 42
def execEvent (_ : Unit) : UInt32 := u 43
def forkEvent (_ : Unit) : UInt32 := u 44
def vforkEvent (_ : Unit) : UInt32 := u 45
def cloneEvent (_ : Unit) : UInt32 := u 46
def seccompEvent (_ : Unit) : UInt32 := u 47
def stackReserve (_ : Unit) : Nat := n 93
def pathLimit (_ : Unit) : Nat := n 94
def scriptHeaderSize (_ : Unit) : Nat := n 95
def stopEvent (_ : Unit) : UInt32 := u 48

def registerLayout (_ : Unit) : LeanSudo.Intercept.RegisterLayout where
  nativeSize := n 49
  compatSize := n 50
  nativeArgs := #[n 51, n 52, n 53]
  compatArgs := #[n 54, n 55, n 56]
  nativeCompatArgs := #[n 57, n 58, n 59]
  nativeSp := n 60
  compatSp := n 61
  nativeSyscall := n 62
  compatSyscall := n 63
  nativeReturn := n 64
  compatReturn := n 65
  nativeWidth := n 66
  compatWidth := n 67
  nativePointerWidth := pointerBytes ()
  compatPointerWidth := intBytes ()

def seccompConfig (arch : LeanSudo.Intercept.Seccomp.Architecture) :
    LeanSudo.Intercept.Seccomp.Config where
  arch
  nativeArch := u 68
  compatArch := u 69
  execve := u 70
  execveat := u 71
  compatExecve := u 72
  compatExecveat := u 73
  x32Execve := u 74
  x32Execveat := u 75
  retTrace := u 76
  retAllow := u 77
  retKill := u 78
  loadCode := n 79
  jumpCode := n 80
  returnCode := n 81
  archOffset := n 82
  syscallOffset := n 83
  filterSize := n 84
  codeOffset := n 85
  codeWidth := n 86
  yesOffset := n 87
  yesWidth := n 88
  noOffset := n 89
  noWidth := n 90
  valueOffset := n 91
  valueWidth := n 92

@[extern "lean_intercept_arch"]
opaque architecture : IO UInt8

@[extern "lean_intercept_page_size"]
opaque pageSize : IO UInt64

@[extern "lean_intercept_ptrace"]
private opaque ptraceRaw (request pid : UInt32) (address data : UInt64) :
    IO (UInt32 × UInt64)

def ptraceAllowed (request : UInt32) : Bool :=
  request != 0 && (request == peek () || request == poke () ||
    request == stepSyscall () || request == resume () || request == seize () ||
    request == traceListen () || request == detach () || request == interrupt ())

theorem ptrace_allowed_requests (request : UInt32) :
    ptraceAllowed request = true ↔ request ≠ 0 ∧
      (request = peek () ∨ request = poke () ∨ request = stepSyscall () ∨
        request = resume () ∨ request = seize () ∨ request = traceListen () ∨
        request = detach () ∨ request = interrupt ()) := by
  simp [ptraceAllowed, Bool.or_eq_true, or_assoc]

def ptraceResult (request pid : UInt32) (address data : UInt64) :
    IO (UInt32 × UInt64) := do
  if !ptraceAllowed request then return (Posix.EINVAL (), 0)
  ptraceRaw request pid address data

private def checkError (error : UInt32) : IO Unit := do
  if error != 0 then CoreFacts.failErrno error.toNat

private def checkedValue {α : Type} (result : UInt32 × α) : IO α := do
  let (error, value) := result
  checkError error
  return value

private def checkedFd (result : Int32) : IO UInt32 := do
  if result < 0 then CoreFacts.failErrno result.toInt
  return result.toUInt32

def ptrace (request pid : UInt32) (address data : UInt64) : IO UInt64 := do
  let (error, value) ← ptraceResult request pid address data
  if error ≠ 0 then throw (IO.userError "command interception failed")
  return value

@[extern "lean_intercept_regset"]
private opaque regsetRaw (pid note size : UInt32) : IO (UInt32 × ByteArray)

def regset (pid note size : UInt32) : IO ByteArray := do
  checkedValue (← regsetRaw pid note size)

@[extern "lean_intercept_set_regset"]
private opaque setRegsetRaw (pid note : UInt32) (bytes : @& ByteArray) : IO UInt32

def setRegset (pid note : UInt32) (bytes : ByteArray) : IO Unit := do
  checkError (← setRegsetRaw pid note bytes)

@[extern "lean_intercept_event"]
private opaque eventRaw (pid : UInt32) : IO (UInt32 × UInt64)

def event (pid : UInt32) : IO UInt64 := do checkedValue (← eventRaw pid)

@[extern "lean_intercept_memory"]
opaque memory (pid : UInt32) (address : UInt64) (size : UInt32) : IO (UInt32 × ByteArray)

@[extern "lean_intercept_read"]
opaque read (fd size : UInt32) : IO (UInt32 × ByteArray)

@[extern "lean_intercept_write"]
opaque send (fd : UInt32) (bytes : @& ByteArray) (offset : UInt32) : IO Int64

@[extern "lean_intercept_open"]
private opaque openFileRaw (path : @& String) (flags : UInt32) : IO Int32

def openFile (path : String) (flags : UInt32) : IO UInt32 := do
  checkedFd (← openFileRaw path flags)

@[extern "lean_intercept_close"]
private opaque closeRaw (fd : UInt32) : IO UInt32

def close (fd : UInt32) : IO Unit := do checkError (← closeRaw fd)

@[extern "lean_intercept_readlink"]
private opaque readlinkRaw (path : @& String) (size : UInt32) : IO (UInt32 × ByteArray)

def readlink (path : String) (size : UInt32) : IO ByteArray := do
  checkedValue (← readlinkRaw path size)

@[extern "lean_intercept_socket"]
private opaque socketRaw (family kind : UInt32) : IO Int32

def socket (family kind : UInt32) : IO UInt32 := do checkedFd (← socketRaw family kind)

@[extern "lean_intercept_bind"]
private opaque bindRaw (fd : UInt32) (address : @& ByteArray) : IO UInt32

def bind (fd : UInt32) (address : ByteArray) : IO Unit := do checkError (← bindRaw fd address)

@[extern "lean_intercept_sockname"]
private opaque socknameRaw (fd : UInt32) : IO (UInt32 × ByteArray)

def sockname (fd : UInt32) : IO ByteArray := do checkedValue (← socknameRaw fd)

@[extern "lean_intercept_listen"]
private opaque listenRaw (fd : UInt32) : IO UInt32

def listen (fd : UInt32) : IO Unit := do checkError (← listenRaw fd)

@[extern "lean_intercept_accept"]
private opaque acceptRaw (fd : UInt32) : IO (Int32 × ByteArray)

def accept (fd : UInt32) : IO (UInt32 × ByteArray) := do
  let (child, bytes) ← acceptRaw fd
  return (← checkedFd child, bytes)

@[extern "lean_intercept_socketpair"]
private opaque socketpairRaw : IO (Int32 × UInt32)

def socketpair : IO (UInt32 × UInt32) := do
  let (first, second) ← socketpairRaw
  return (← checkedFd first, second)

@[extern "lean_intercept_fcntl"]
private opaque fcntlRaw (fd op value : UInt32) : IO Int32

def fcntl (fd op value : UInt32) : IO UInt32 := do checkedFd (← fcntlRaw fd op value)

@[extern "lean_intercept_sockopt"]
private opaque sockoptRaw (fd level option value : UInt32) : IO UInt32

def sockopt (fd level option value : UInt32) : IO Unit := do
  checkError (← sockoptRaw fd level option value)

@[extern "lean_intercept_poll"]
opaque pollResult (fd events : UInt32) : IO (UInt32 × UInt32)

def poll (fd events : UInt32) : IO UInt32 := do
  let (error, ready) ← pollResult fd events
  if error = Posix.EINTR () then return 0
  if error ≠ 0 then throw (IO.userError "command interception failed")
  return ready

@[extern "lean_intercept_kill"]
private opaque killRaw (pid signal : UInt32) : IO UInt32

def kill (pid signal : UInt32) : IO Unit := do checkError (← killRaw pid signal)

@[extern "lean_intercept_wait"]
opaque wait : IO (Int64 × UInt32)

def traceSupported : IO Bool := do
  if (← architecture) = 0 then return false
  try
    let fd ← openFile "/proc/sys/kernel/seccomp/actions_avail"
      (Posix.O_RDONLY () ||| Posix.O_CLOEXEC ())
    try
      let mut bytes := ByteArray.empty
      for _ in [:1024] do
        if bytes.size ≥ 511 then return false
        let (error, chunk) ← read fd (511 - bytes.size).toUInt32
        if error = Posix.EINTR () then continue
        if error ≠ 0 then return false
        if chunk.isEmpty then
          let some text := String.fromUTF8? bytes | return false
          let text := String.ofList (text.toList.map fun c =>
            if " \t\r\n".contains c then ' ' else c)
          return (text.splitOn " ").contains "trap"
        bytes := bytes ++ chunk
      return false
    finally close fd
  catch _ => return false

end LeanSudo.Sys.Prim.Intercept
