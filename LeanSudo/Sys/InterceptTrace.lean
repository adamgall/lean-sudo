import LeanSudo.Intercept.Registers
import LeanSudo.Sys.Prim.Intercept
import LeanSudo.Sys.Core
import LeanSudo.Sys.LogSrv

namespace LeanSudo.Sys.InterceptTrace

open LeanSudo.Intercept
open Registers
open Prim.Posix

namespace P
export Prim.Intercept
  (memory ptrace regset setRegset event read send openFile close readlink kill
   wordBytes pointerBytes intBytes registerNote armSyscallNote noSyscall accessDenied
   peek poke stepSyscall resume seize traceOptions traceListen detach interrupt
   execEvent forkEvent vforkEvent cloneEvent seccompEvent stopEvent
   stopMask signalMask stoppedValue signalShift eventShift trapSignal syscallTrap
   setidBits noChild stackReserve pathLimit scriptHeaderSize)
end P

structure Request where
  command : String
  cwd : String
  argv : Array String
  env : Array String
  pid : UInt32
  setid : Bool
  deriving Repr

def Request.byteSize (request : Request) : Nat :=
  request.command.toUTF8.size + request.cwd.toUTF8.size +
    request.argv.foldl (fun size text => size + text.toUTF8.size) 0 +
    request.env.foldl (fun size text => size + text.toUTF8.size) 0

def Request.bounded (request : Request) : Bool :=
  request.byteSize ≤ 4194304 && request.argv.size ≤ 1048576 && request.env.size ≤ 1048576

theorem Request.bounded_bytes (request : Request) (h : request.bounded = true) :
    request.byteSize ≤ 4194304 := by
  simp only [Request.bounded, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1

structure Expected where
  dev : Nat
  ino : Nat
  argv : Array String
  env : Array String

structure Task where
  pid : UInt32
  newborn : Bool := false
  denied : Bool := false
  status : UInt32 := 0
  expected : Option Expected := none

structure State where
  arch : Seccomp.Architecture
  config : Seccomp.Config
  layout : RegisterLayout
  pageSize : Nat
  verify : Bool
  initial : Bool := true
  root : Option UInt32 := none
  tasks : Array Task := #[]

def failure : IO α := throw (IO.userError "command interception failed")

def decode (bytes : ByteArray) : IO String :=
  match String.fromUTF8? bytes with
  | some text => if text.contains '\x00' then failure else pure text
  | none => failure

def remote (pid : UInt32) (address size : Nat) : IO ByteArray := do
  if address = 0 || address + size ≥ 2 ^ (P.pointerBytes () * 8) then failure
  let (error, bytes) ← P.memory pid address.toUInt64 size.toUInt32
  if error = 0 && bytes.size = size then return bytes
  let mut result := ByteArray.empty
  let mut offset := 0
  let width := P.wordBytes ()
  for _ in [:size / width + 2] do
    if offset = size then return result
    let position := address + offset
    let aligned := position / width * width
    let skip := position % width
    let count := min (width - skip) (size - offset)
    let value ← P.ptrace (P.peek ()) pid aligned.toUInt64 0
    let bytes : ByteArray := ⟨(Seccomp.little width value.toNat).toArray⟩
    result := result ++ bytes.extract skip (skip + count)
    offset := offset + count
  failure

def remoteWrite (pid : UInt32) (address : Nat) (bytes : ByteArray) : IO Unit := do
  if address = 0 || address + bytes.size ≥ 2 ^ (P.pointerBytes () * 8) then failure
  let mut offset := 0
  let width := P.wordBytes ()
  for _ in [:bytes.size / width + 2] do
    if offset = bytes.size then return
    let position := address + offset
    let aligned := position / width * width
    let skip := position % width
    let count := min (width - skip) (bytes.size - offset)
    let original ← if skip = 0 && count = width then pure 0
      else P.ptrace (P.peek ()) pid aligned.toUInt64 0
    let mut data : ByteArray := ⟨(Seccomp.little width original.toNat).toArray⟩
    for i in [:count] do
      data := data.set! (skip + i) (bytes[offset + i]?.getD 0)
    let _ ← P.ptrace (P.poke ()) pid aligned.toUInt64 (word data 0 width).toUInt64
    offset := offset + count
  failure

def remoteString (pageSize : Nat) (pid : UInt32) (address budget : Nat) :
    IO (String × Nat) := do
  let mut bytes := ByteArray.empty
  let mut used := 0
  for _ in [:min budget 2097152] do
    let count := min 256 (min (pageSize - (address + used) % pageSize) (budget - used))
    if count = 0 || used ≥ 2097152 then failure
    let chunk ← remote pid (address + used) count
    let endPos := chunk.data.toList.idxOf 0
    if endPos < chunk.size then
      return (← decode (bytes ++ chunk.extract 0 endPos), budget - used - endPos - 1)
    bytes := bytes ++ chunk
    used := used + count
  failure

def remoteVector (pageSize : Nat) (pid : UInt32) (address width budget : Nat) :
    IO (Array String × Nat) := do
  if address = 0 then return (#[], budget)
  let mut result := #[]
  let mut remaining := budget
  for i in [:budget / width + 1] do
    if remaining < width then failure
    let pointer := word (← remote pid (address + i * width) width) 0 width
    remaining := remaining - width
    if pointer = 0 then return (result, remaining)
    let (text, next) ← remoteString pageSize pid pointer remaining
    result := result.push text
    remaining := next
  failure

def getRegs (config : Seccomp.Config) (layout : RegisterLayout)
    (pid : UInt32) (abi : Nat) : IO Registers := do
  let bytes ← P.regset pid (P.registerNote ()) (max layout.nativeSize layout.compatSize).toUInt32
  if !Registers.valid config.arch layout bytes abi then failure
  return { config, layout, bytes, abi }

def putRegs (pid : UInt32) (r : Registers) : IO Unit :=
  P.setRegset pid (P.registerNote ()) r.bytes

def skipExec (pid : UInt32) (r : Registers) : IO Unit := do
  putRegs pid (r.skip (P.noSyscall ()))
  if r.arch = .aarch64 then
    let bytes : ByteArray := ⟨Array.replicate (P.intBytes ()) 255⟩
    P.setRegset pid (P.armSyscallNote ()) bytes

def procPath (pid : UInt32) (name : String) : String := s!"/proc/{pid}/{name}"

def readBytes (fd : UInt32) (size : Nat) : IO ByteArray := do
  for _ in [:1024] do
    let (error, bytes) ← P.read fd size.toUInt32
    if error = 0 then return bytes
    if error ≠ EINTR () then failure
  failure

def fileBytes (path : String) (limit : Nat := 8388608) : IO ByteArray := do
  let fd ← P.openFile path (O_RDONLY () ||| O_CLOEXEC ())
  try
    let mut result := ByteArray.empty
    for _ in [:limit / 4096 + 2] do
      let bytes ← readBytes fd (min 4096 (limit + 1 - result.size))
      if bytes.isEmpty then return result
      result := result ++ bytes
      if result.size > limit then failure
    failure
  finally P.close fd

def vectorBytes (values : Array String) : ByteArray :=
  values.foldl (fun bytes value => bytes ++ value.toUTF8 |>.push 0) ByteArray.empty

def verifyExec (task : Task) (expected : Expected) : IO Bool := do
  let some image ← stat (procPath task.pid "exe") | return false
  if image.dev ≠ expected.dev || image.ino ≠ expected.ino then return false
  return (← fileBytes (procPath task.pid "cmdline")) == vectorBytes expected.argv &&
    (← fileBytes (procPath task.pid "environ")) == vectorBytes expected.env

def execPath (raw cwd : String) : IO String := do
  if raw.isEmpty then failure
  if raw.startsWith "/" then return raw
  let joined := s!"{cwd}/{raw}"
  if joined.toUTF8.size ≥ P.pathLimit () then failure
  let parts := joined.splitOn "/"
  let base := parts.getLast!
  let parent := String.intercalate "/" parts.dropLast
  let some resolved ← realpath (if parent.isEmpty then "/" else parent) | failure
  return resolved ++ (if resolved = "/" then "" else "/") ++ base

def expectedImage (command label cwd : String) (argv env : Array String)
    (requested : FileStat) : IO Expected := do
  let mut command := command
  let mut label := label
  let mut argv := argv
  for depth in [:5] do
    let fd ← P.openFile command (O_RDONLY () ||| O_CLOEXEC ())
    let (header, image) ← try
      let header ← readBytes fd (P.scriptHeaderSize ())
      let some image ← stat s!"/proc/self/fd/{fd}" | failure
      pure (header, image)
    finally P.close fd
    if !image.isReg then failure
    if depth = 0 && (image.dev ≠ requested.dev || image.ino ≠ requested.ino) then failure
    if header[0]?.getD 0 ≠ 35 || header[1]?.getD 0 ≠ 33 then
      return { dev := image.dev, ino := image.ino, argv, env }
    if depth = 4 then failure
    let newline := header.data.toList.idxOf 10
    if newline = header.size && header.size = P.scriptHeaderSize () then failure
    let line ← decode (header.extract 2 newline)
    let chars := line.toList.dropWhile (fun c => c = ' ' || c = '\t')
    let chars := (chars.reverse.dropWhile (fun c => c = ' ' || c = '\t')).reverse
    let interpreter := String.ofList (chars.takeWhile (fun c => c ≠ ' ' && c ≠ '\t'))
    if interpreter.isEmpty then failure
    let option := String.ofList ((chars.drop interpreter.length).dropWhile
      (fun c => c = ' ' || c = '\t'))
    argv := #[interpreter] ++ (if option.isEmpty then #[] else #[option]) ++
      #[label] ++ argv.extract 1 argv.size
    label := interpreter
    command := if interpreter.startsWith "/" then interpreter else s!"{cwd}/{interpreter}"
  failure

def rewritePath (pageSize : Nat) (pid : UInt32) (r : Registers) (command : String)
    (argv env : Array String) : IO Unit := do
  let bytes := command.toUTF8.push 0
  let width := P.wordBytes ()
  let space := (bytes.size + width - 1) / width * width
  let sp := r.stackPointer
  if sp < P.stackReserve () + space then failure
  let address := sp - P.stackReserve () - space
  if r.abi = 1 && address ≥ 2 ^ (r.layout.compatPointerWidth * 8) then failure
  remoteWrite pid address bytes
  let changed := r.setArg 0 address
  putRegs pid changed
  let actual ← getRegs r.config r.layout pid r.abi
  if actual.compat ≠ r.compat || actual.syscall ≠ r.config.execve.toNat ||
      actual.arg 0 ≠ address || actual.arg 1 ≠ r.arg 1 || actual.arg 2 ≠ r.arg 2 then failure
  if (← remote pid address bytes.size) ≠ bytes then failure
  let (args, _) ← remoteVector pageSize pid (actual.arg 1) r.pointerWidth 8388608
  let (environment, _) ← remoteVector pageSize pid (actual.arg 2) r.pointerWidth 8388608
  if args ≠ argv || environment ≠ env then failure

def checkExec (state : State) (check : Request → IO Bool) (task : Task) : IO Task := do
  let abi := (← P.event task.pid).toNat
  let r ← getRegs state.config state.layout task.pid abi
  let nr := r.syscall
  if nr ≠ state.config.execve.toNat && nr ≠ state.config.execveat.toNat then
    failure
  let task := { task with expected := none }
  if state.initial then return task
  if nr = state.config.execveat.toNat then return task
  let approved ← try
    let (raw, budget) ← remoteString state.pageSize task.pid (r.arg 0) 8388608
    let (rawArgs, budget) ← remoteVector state.pageSize task.pid (r.arg 1) r.pointerWidth budget
    let (env, _) ← remoteVector state.pageSize task.pid (r.arg 2) r.pointerWidth budget
    let argv := if rawArgs.isEmpty then #[""] else rawArgs
    let cwd ← decode (← P.readlink (procPath task.pid "cwd") (P.pathLimit ()).toUInt32)
    if !cwd.startsWith "/" || cwd.toUTF8.size ≥ P.pathLimit () - 1 then failure
    let command ← execPath raw cwd
    let path := if raw.startsWith "/" then procPath task.pid ("root" ++ raw)
      else procPath task.pid ("cwd/" ++ raw)
    let some image ← stat path | failure
    let expected ← if state.verify then do
      let some image ← stat command | failure
      pure (some image)
      else pure none
    let request : Request := {
      command, cwd, argv, env, pid := task.pid
      setid := image.mode &&& P.setidBits () ≠ 0 }
    if !request.bounded then failure
    if !(← check request) then pure none else do
      if !raw.startsWith "/" then rewritePath state.pageSize task.pid r command rawArgs env
      let expected ← expected.mapM (expectedImage command raw cwd argv env)
      pure (some { task with expected })
  catch _ => pure none
  LogSrv.poll
  match approved with
  | some task => pure task
  | none =>
    skipExec task.pid r
    let _ ← P.ptrace (P.stepSyscall ()) task.pid 0 0
    pure { task with denied := true, status := 0 }

def putTask (state : State) (task : Task) : State :=
  match state.tasks.findIdx? (fun t => t.pid == task.pid) with
  | some i => { state with tasks := state.tasks.set! i task }
  | none => { state with tasks := state.tasks.push task }

def removeTask (state : State) (pid : UInt32) : State :=
  { state with tasks := state.tasks.filter (fun t => t.pid != pid) }

def forked (state : State) (pid : UInt32) : IO State := do
  let child ← P.event pid
  if child = 0 || child.toNat > (INT_MAX ()).toNat then failure
  if state.tasks.any (fun t => t.pid.toUInt64 == child) then return state
  return putTask state { pid := child.toUInt32, newborn := true }

def stopped (state : State) (pid status : UInt32) : IO (State × Task) := do
  let mut state := state
  if status >>> P.eventShift () = P.execEvent () then
    let old ← P.event pid
    if old ≠ pid.toUInt64 then
      let some task := state.tasks.find? (fun t => t.pid.toUInt64 == old) | failure
      state := removeTask (removeTask state pid) task.pid
      state := putTask state { task with pid }
  match state.tasks.find? (fun t => t.pid == pid) with
  | some task => return (state, { task with status })
  | none =>
    if status >>> P.eventShift () ≠ P.stopEvent () then failure
    return (state, { pid, status, newborn := true })

def attach (ref : IO.Ref State) (pid : UInt32) : IO Unit := do
  let state ← ref.get
  if state.root.isSome || pid = 0 then failure
  let _ ← P.ptrace (P.seize ()) pid 0 (P.traceOptions ())
  ref.set (putTask { state with root := some pid, initial := true } { pid })

def childEvent (ref : IO.Ref State) (check : Request → IO Bool)
    (pid status : UInt32) : IO Bool := do
  let state ← ref.get
  try
    if status &&& P.signalMask () ≠ P.stoppedValue () then
      ref.set (removeTask state pid)
      return state.root ≠ some pid
    if status &&& P.stopMask () ≠ P.stoppedValue () then return state.root ≠ some pid
    let event := status >>> P.eventShift ()
    let signal := status >>> P.signalShift () &&& P.stopMask ()
    if event = 0 && !(state.tasks.any (fun t => t.pid == pid)) then return true
    let (state, task) ← stopped state pid status
    ref.set (putTask state task)
    let mut state := state
    let mut task := task
    let mut deliver := 0
    if event = P.seccompEvent () then
      task ← checkExec state check task
      state := { state with initial := false }
      if task.denied && task.status = 0 then
        ref.set (putTask state task)
        return true
    else if event = P.execEvent () then
      if let some expected := task.expected then
        let verified ← try verifyExec task expected catch _ => pure false
        if !verified then
          try P.kill pid (SIGKILL ()) catch _ => pure ()
          let _ ← Prim.Intercept.ptraceResult (P.resume ()) pid 0 (SIGKILL ()).toUInt64
          ref.set (putTask state { task with status := 0, expected := none })
          return true
      task := { task with expected := none }
    else if event = P.forkEvent () || event = P.vforkEvent () || event = P.cloneEvent () then
      state ← forked state pid
      ref.set (putTask state task)
    else if signal = P.trapSignal () ||| P.syscallTrap () && task.denied then
      let size := max state.layout.nativeSize state.layout.compatSize
      let bytes ← P.regset pid (P.registerNote ()) size.toUInt32
      let abi := if bytes.size = state.layout.compatSize then 1 else 0
      if !Registers.valid state.arch state.layout bytes abi then failure
      let regs : Registers := { config := state.config, layout := state.layout, bytes, abi }
      putRegs pid (regs.setReturn (-Int.ofNat (P.accessDenied ())))
      task := { task with denied := false }
    else if event = P.stopEvent () then
      if task.newborn then task := { task with newborn := false }
      else if signal = SIGSTOP () || signal = SIGTSTP () ||
          signal = SIGTTIN () || signal = SIGTTOU () then
        let _ ← P.ptrace (P.traceListen ()) pid 0 0
        ref.set (putTask state { task with status := 0 })
        return state.root ≠ some pid
    else if event = 0 then deliver := signal
    else failure
    let (error, _) ← Prim.Intercept.ptraceResult
      (if task.denied then P.stepSyscall () else P.resume ()) pid 0 deliver.toUInt64
    if error ≠ 0 && error ≠ ESRCH () then failure
    ref.set (putTask state { task with status := 0 })
    return true
  catch error =>
    try P.kill pid (SIGKILL ()) catch _ => pure ()
    throw error

private def detachStopped (state : State) (task : Task) : IO State := do
  let event := task.status >>> P.eventShift ()
  let signal := task.status >>> P.signalShift () &&& P.stopMask ()
  let mut state := state
  let mut deliver := 0
  let failed ← try
    if event = P.seccompEvent () then
      let abi := (← P.event task.pid).toNat
      skipExec task.pid (← getRegs state.config state.layout task.pid abi)
    else if event = P.execEvent () then
      if let some expected := task.expected then
        if !(← verifyExec task expected) then failure
    else if event = P.forkEvent () || event = P.vforkEvent () || event = P.cloneEvent () then
      state ← forked state task.pid
    else if event = 0 && signal = P.trapSignal () ||| P.syscallTrap () then
      if !task.denied then failure
      let size := max state.layout.nativeSize state.layout.compatSize
      let bytes ← P.regset task.pid (P.registerNote ()) size.toUInt32
      let abi := if bytes.size = state.layout.compatSize then 1 else 0
      if !Registers.valid state.arch state.layout bytes abi then failure
      let regs : Registers := { config := state.config, layout := state.layout, bytes, abi }
      putRegs task.pid (regs.setReturn (-Int.ofNat (P.accessDenied ())))
    else if event = 0 then deliver := signal
    else if event ≠ P.stopEvent () then failure
    pure false
  catch _ => pure true
  if failed then
    try P.kill task.pid (SIGKILL ()) catch _ => pure ()
  let (error, _) ← Prim.Intercept.ptraceResult (P.detach ()) task.pid 0
    (if failed then (SIGKILL ()).toUInt64 else deliver.toUInt64)
  if error ≠ 0 && error ≠ ESRCH () then
    try P.kill task.pid (SIGKILL ()) catch _ => pure ()
  return removeTask state task.pid

private partial def drain (state : State) : IO State := do
  if state.tasks.isEmpty then return { state with root := none }
  if let some task := state.tasks.find? (fun task => task.status ≠ 0) then
    return ← drain (← detachStopped state task)
  let (pid, status) ← Prim.Intercept.wait
  if pid = -(EINTR ()).toNat.toInt64 then return ← drain state
  if pid < 0 then
    for task in state.tasks do
      if pid ≠ -(P.noChild ()) then
        try P.kill task.pid (SIGKILL ()) catch _ => pure ()
    return { state with tasks := #[], root := none }
  let pid := pid.toInt.toNat.toUInt32
  if status &&& P.signalMask () ≠ P.stoppedValue () then return ← drain (removeTask state pid)
  if status &&& P.stopMask () ≠ P.stoppedValue () then return ← drain state
  if !(state.tasks.any (fun task => task.pid == pid)) && status >>> P.eventShift () = 0 then
    return ← drain state
  let next ← try
    let (state, task) ← stopped state pid status
    pure (putTask state task)
  catch _ =>
    try P.kill pid (SIGKILL ()) catch _ => pure ()
    pure (removeTask state pid)
  drain next

def close (ref : IO.Ref State) : IO Unit := do
  let state ← ref.get
  for task in state.tasks do
    if task.status = 0 then
      let (error, _) ← Prim.Intercept.ptraceResult (P.interrupt ()) task.pid 0 0
      if error ≠ 0 && error ≠ ESRCH () then
        try P.kill task.pid (SIGKILL ()) catch _ => pure ()
  ref.set (← drain state)

end LeanSudo.Sys.InterceptTrace
