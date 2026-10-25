import LeanSudo.Intercept.Seccomp

namespace LeanSudo.Intercept

structure RegisterLayout where
  nativeSize : Nat
  compatSize : Nat
  nativeArgs : Array Nat
  compatArgs : Array Nat
  nativeCompatArgs : Array Nat
  nativeSp : Nat
  compatSp : Nat
  nativeSyscall : Nat
  compatSyscall : Nat
  nativeReturn : Nat
  compatReturn : Nat
  nativeWidth : Nat
  compatWidth : Nat
  nativePointerWidth : Nat
  compatPointerWidth : Nat

structure Registers where
  config : Seccomp.Config
  layout : RegisterLayout
  bytes : ByteArray
  abi : Nat

namespace Registers

def word (bytes : ByteArray) (offset width : Nat) : Nat :=
  (List.range width).foldl (fun value i =>
    value + (bytes[offset + i]?.getD 0).toNat * 2 ^ (8 * i)) 0

def putWord := Seccomp.put

def arch (r : Registers) : Seccomp.Architecture := r.config.arch

def compat (r : Registers) : Bool := r.bytes.size == r.layout.compatSize

def width (r : Registers) : Nat :=
  if r.compat then r.layout.compatWidth else r.layout.nativeWidth

def pointerWidth (r : Registers) : Nat :=
  if r.abi = 0 then r.layout.nativePointerWidth else r.layout.compatPointerWidth

def valid (arch : Seccomp.Architecture) (layout : RegisterLayout)
    (bytes : ByteArray) (abi : Nat) : Bool :=
  if arch = .x86_64 then
    (bytes.size == layout.nativeSize && abi ≤ 2) ||
      (bytes.size == layout.compatSize && abi == 1)
  else (bytes.size == layout.nativeSize && abi == 0) ||
    (bytes.size == layout.compatSize && abi == 1)

theorem valid_x86_compat (layout : RegisterLayout) (bytes : ByteArray) (abi : Nat)
    (distinct : layout.compatSize ≠ layout.nativeSize) (size : bytes.size = layout.compatSize)
    (accepted : valid .x86_64 layout bytes abi = true) : abi = 1 := by
  simpa [valid, size, distinct] using accepted

theorem valid_arm_compat (layout : RegisterLayout) (bytes : ByteArray) (abi : Nat)
    (distinct : layout.compatSize ≠ layout.nativeSize) (size : bytes.size = layout.compatSize)
    (accepted : valid .aarch64 layout bytes abi = true) : abi = 1 := by
  simpa [valid, size, distinct] using accepted

def argOffset (r : Registers) (n : Nat) : Nat :=
  if r.compat then r.layout.compatArgs[n]?.getD 0
  else if r.abi = 1 then r.layout.nativeCompatArgs[n]?.getD 0
  else r.layout.nativeArgs[n]?.getD 0

def arg (r : Registers) (n : Nat) : Nat :=
  let value := word r.bytes (r.argOffset n) r.width
  if r.abi = 1 then value % 2 ^ (r.layout.compatPointerWidth * 8) else value

theorem arg_compat_width (r : Registers) (n : Nat) (compat : r.abi = 1) :
    r.arg n < 2 ^ (r.layout.compatPointerWidth * 8) := by
  simp only [arg, compat, ↓reduceIte]
  exact Nat.mod_lt _ (Nat.pow_pos (by decide))

def setArg (r : Registers) (n value : Nat) : Registers :=
  { r with
    bytes := putWord r.bytes (r.argOffset n) r.width
      (if r.abi = 1 then value % 2 ^ (r.layout.compatPointerWidth * 8) else value) }

def stackPointer (r : Registers) : Nat :=
  word r.bytes (if r.compat then r.layout.compatSp else r.layout.nativeSp) r.width

def syscallOffset (r : Registers) : Nat :=
  if r.compat then r.layout.compatSyscall else r.layout.nativeSyscall

def syscall (r : Registers) : Nat :=
  let nr := word r.bytes r.syscallOffset r.width
  if r.abi = 2 then
    if nr = r.config.x32Execve.toNat then r.config.execve.toNat
    else if nr = r.config.x32Execveat.toNat then r.config.execveat.toNat
    else 2 ^ (r.width * 8) - 1
  else if r.abi = 1 then
    if nr = r.config.compatExecve.toNat then r.config.execve.toNat
    else if nr = r.config.compatExecveat.toNat then r.config.execveat.toNat
    else 2 ^ (r.width * 8) - 1
  else nr

def setReturn (r : Registers) (value : Int) : Registers :=
  let offset := if r.compat then r.layout.compatReturn else r.layout.nativeReturn
  { r with
    bytes := putWord r.bytes offset r.width (value % (2 ^ (r.width * 8) : Int)).toNat }

def skip (r : Registers) (notImplemented : Nat) : Registers :=
  if r.arch = .x86_64 then
    { r with bytes := putWord r.bytes r.syscallOffset r.width (2 ^ (r.width * 8) - 1) }
  else r.setReturn (-Int.ofNat notImplemented)

end Registers
end LeanSudo.Intercept
