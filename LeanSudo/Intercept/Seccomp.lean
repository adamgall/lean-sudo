import Std

namespace LeanSudo.Intercept.Seccomp

inductive Architecture where
  | x86_64
  | aarch64
  deriving DecidableEq, Repr

structure Config where
  arch : Architecture
  nativeArch : UInt32
  compatArch : UInt32
  execve : UInt32
  execveat : UInt32
  compatExecve : UInt32
  compatExecveat : UInt32
  x32Execve : UInt32
  x32Execveat : UInt32
  retTrace : UInt32
  retAllow : UInt32
  retKill : UInt32
  loadCode : Nat
  jumpCode : Nat
  returnCode : Nat
  archOffset : Nat
  syscallOffset : Nat
  filterSize : Nat
  codeOffset : Nat
  codeWidth : Nat
  yesOffset : Nat
  yesWidth : Nat
  noOffset : Nat
  noWidth : Nat
  valueOffset : Nat
  valueWidth : Nat

inductive Verdict where
  | trace (abi : Nat)
  | allow
  | kill
  deriving DecidableEq, Repr

inductive Instruction where
  | arch
  | syscall
  | equal (value : UInt32) (yes no : Nat)
  | result (value : Verdict)
  deriving Repr

def instructions (c : Config) : List Instruction :=
  [.arch, .equal c.compatArch 0 5, .syscall,
   .equal c.compatExecve 1 0, .equal c.compatExecveat 0 1,
   .result (.trace 1), .result .allow,
   .equal c.nativeArch 1 0, .result .kill, .syscall] ++
  (if c.arch = .x86_64 then
    [.equal c.x32Execve 1 0, .equal c.x32Execveat 0 1, .result (.trace 2)] else []) ++
  [.equal c.execve 1 0, .equal c.execveat 0 1, .result (.trace 0), .result .allow]

def evaluate (arch syscall : UInt32) : Nat → UInt32 → List Instruction → Verdict
  | 0, _, _ => .kill
  | _ + 1, _, [] => .kill
  | fuel + 1, _, .arch :: rest => evaluate arch syscall fuel arch rest
  | fuel + 1, _, .syscall :: rest => evaluate arch syscall fuel syscall rest
  | fuel + 1, acc, .equal value yes no :: rest =>
    evaluate arch syscall fuel acc (rest.drop (if acc = value then yes else no))
  | _ + 1, _, .result value :: _ => value

def verdict (c : Config) (arch nr : UInt32) : Verdict :=
  if arch = c.compatArch then
    if nr = c.compatExecve ∨ nr = c.compatExecveat then .trace 1 else .allow
  else if arch = c.nativeArch then
    if c.arch = .x86_64 ∧ (nr = c.x32Execve ∨ nr = c.x32Execveat) then .trace 2
    else if nr = c.execve ∨ nr = c.execveat then .trace 0 else .allow
  else .kill

theorem instructions_verdict (c : Config) (arch nr : UInt32) :
    evaluate arch nr 20 0 (instructions c) = verdict c arch nr := by
  unfold instructions
  split
  all_goals
    repeat first
    | solve | simp_all [evaluate, verdict]
    | (simp_all [evaluate, verdict]; split)

def traps (c : Config) (arch nr : UInt32) : Prop :=
  (arch = c.compatArch ∧ (nr = c.compatExecve ∨ nr = c.compatExecveat)) ∨
  (arch ≠ c.compatArch ∧ arch = c.nativeArch ∧
    (nr = c.execve ∨ nr = c.execveat ∨
      (c.arch = .x86_64 ∧ (nr = c.x32Execve ∨ nr = c.x32Execveat))))

theorem trap_syscalls (c : Config) (arch nr : UInt32) :
    (evaluate arch nr 20 0 (instructions c) = .trace 0 ∨
     evaluate arch nr 20 0 (instructions c) = .trace 1 ∨
     evaluate arch nr 20 0 (instructions c) = .trace 2) ↔ traps c arch nr := by
  rw [instructions_verdict]
  by_cases hc : arch = c.compatArch <;>
    by_cases hn : arch = c.nativeArch <;>
    by_cases cp : nr = c.compatExecve ∨ nr = c.compatExecveat <;>
    by_cases np : nr = c.execve ∨ nr = c.execveat <;>
    by_cases xp : nr = c.x32Execve ∨ nr = c.x32Execveat <;>
    by_cases xa : c.arch = .x86_64 <;>
    simp_all [verdict, traps]

def little (width : Nat) (value : Nat) : List UInt8 :=
  (List.range width).map fun i => UInt8.ofNat (value / 2 ^ (8 * i))

def put (bytes : ByteArray) (offset width value : Nat) : ByteArray := Id.run do
  let mut bytes := bytes
  for i in [:width] do
    bytes := bytes.set! (offset + i) (UInt8.ofNat (value / 2 ^ (8 * i)))
  return bytes

def resultCode (c : Config) : Verdict → UInt32
  | .trace abi => c.retTrace ||| abi.toUInt32
  | .allow => c.retAllow
  | .kill => c.retKill

def encode (c : Config) (instruction : Instruction) : ByteArray :=
  let (code, yes, no, value) := match instruction with
    | .arch => (c.loadCode, 0, 0, c.archOffset)
    | .syscall => (c.loadCode, 0, 0, c.syscallOffset)
    | .equal value yes no => (c.jumpCode, yes, no, value.toNat)
    | .result result => (c.returnCode, 0, 0, (resultCode c result).toNat)
  let bytes : ByteArray := ⟨Array.replicate c.filterSize 0⟩
  put (put (put (put bytes c.codeOffset c.codeWidth code)
    c.yesOffset c.yesWidth yes) c.noOffset c.noWidth no) c.valueOffset c.valueWidth value

def program (c : Config) : ByteArray :=
  (instructions c).foldl (fun bytes instruction => bytes ++ encode c instruction) ByteArray.empty

end LeanSudo.Intercept.Seccomp
