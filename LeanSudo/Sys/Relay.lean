namespace LeanSudo.Sys

structure RelayHooks where
  onInput : ByteArray → IO Bool := fun _ => pure true
  onOutput : UInt32 → ByteArray → IO Bool := fun _ _ => pure true
  onStream : UInt32 → ByteArray → IO Bool := fun _ _ => pure true
  needsStream : UInt32 → IO Bool := fun _ => pure false
  forcePty : IO Bool := pure false
  onWindow : UInt32 → UInt32 → IO Unit := fun _ _ => pure ()
  onSuspend : UInt32 → IO Unit := fun _ => pure ()
  onSpawn : UInt32 → IO Unit := fun _ => pure ()
  onChild : UInt32 → UInt32 → IO Bool := fun _ _ => pure false
  onSignal : UInt32 → IO Unit := fun _ => pure ()
  onTick : IO Unit := pure ()
  onFinish : UInt32 → IO Unit := fun _ => pure ()
  onExecError : UInt32 → IO Unit := fun _ => pure ()

namespace RelayHooks

def compose (a b : RelayHooks) : RelayHooks where
  onInput := fun bytes => do
    if !(← a.onInput bytes) then return false
    b.onInput bytes
  onOutput := fun fd bytes => do
    if !(← a.onOutput fd bytes) then return false
    b.onOutput fd bytes
  onStream := fun stream bytes => do
    if !(← a.onStream stream bytes) then return false
    b.onStream stream bytes
  needsStream := fun stream => do
    if ← a.needsStream stream then return true
    b.needsStream stream
  forcePty := do
    if ← a.forcePty then return true
    b.forcePty
  onWindow := fun rows cols => a.onWindow rows cols *> b.onWindow rows cols
  onSpawn := fun pid => a.onSpawn pid *> b.onSpawn pid
  onSuspend := fun signal => a.onSuspend signal *> b.onSuspend signal
  onChild := fun pid status => do
    if ← a.onChild pid status then return true
    b.onChild pid status
  onSignal := fun signal => a.onSignal signal *> b.onSignal signal
  onTick := a.onTick *> b.onTick
  onFinish := fun status => a.onFinish status *> b.onFinish status
  onExecError := fun error => a.onExecError error *> b.onExecError error

end RelayHooks
end LeanSudo.Sys
