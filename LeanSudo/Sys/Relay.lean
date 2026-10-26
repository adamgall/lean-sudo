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

def allThen [Monad m] (first second : m Bool) : m Bool := do
  if ← first then second else pure false

def anyThen [Monad m] (first second : m Bool) : m Bool := do
  if ← first then pure true else second

def inOrder [Monad m] (first second : m Unit) : m Unit := do
  first
  second

theorem allThen_abort [Monad m] [LawfulMonad m] (second : m Bool) :
    allThen (pure false) second = pure false := by simp [allThen]

theorem allThen_continue [Monad m] [LawfulMonad m] (second : m Bool) :
    allThen (pure true) second = second := by simp [allThen]

theorem allThen_abort_after [Monad m] [LawfulMonad m] (first : m α) (second : m Bool) :
    allThen (first >>= fun _ => pure false) second = (first >>= fun _ => pure false) := by
  simp [allThen]

theorem allThen_assoc [Monad m] [LawfulMonad m] (a b c : m Bool) :
    allThen (allThen a b) c = allThen a (allThen b c) := by
  simp only [allThen, bind_assoc]
  congr 1
  funext accepted
  cases accepted <;> simp

theorem anyThen_stop [Monad m] [LawfulMonad m] (second : m Bool) :
    anyThen (pure true) second = pure true := by simp [anyThen]

theorem anyThen_continue [Monad m] [LawfulMonad m] (second : m Bool) :
    anyThen (pure false) second = second := by simp [anyThen]

theorem anyThen_stop_after [Monad m] [LawfulMonad m] (first : m α) (second : m Bool) :
    anyThen (first >>= fun _ => pure true) second = (first >>= fun _ => pure true) := by
  simp [anyThen]

theorem anyThen_assoc [Monad m] [LawfulMonad m] (a b c : m Bool) :
    anyThen (anyThen a b) c = anyThen a (anyThen b c) := by
  simp only [anyThen, bind_assoc]
  congr 1
  funext handled
  cases handled <;> simp

theorem inOrder_assoc [Monad m] [LawfulMonad m] (a b c : m Unit) :
    inOrder (inOrder a b) c = inOrder a (inOrder b c) := by
  simp [inOrder, bind_assoc]

def compose (a b : RelayHooks) : RelayHooks where
  onInput := fun bytes => allThen (a.onInput bytes) (b.onInput bytes)
  onOutput := fun fd bytes => allThen (a.onOutput fd bytes) (b.onOutput fd bytes)
  onStream := fun stream bytes => allThen (a.onStream stream bytes) (b.onStream stream bytes)
  needsStream := fun stream => anyThen (a.needsStream stream) (b.needsStream stream)
  forcePty := anyThen a.forcePty b.forcePty
  onWindow := fun rows cols => inOrder (a.onWindow rows cols) (b.onWindow rows cols)
  onSpawn := fun pid => inOrder (a.onSpawn pid) (b.onSpawn pid)
  onSuspend := fun signal => inOrder (a.onSuspend signal) (b.onSuspend signal)
  onChild := fun pid status => anyThen (a.onChild pid status) (b.onChild pid status)
  onSignal := fun signal => inOrder (a.onSignal signal) (b.onSignal signal)
  onTick := inOrder a.onTick b.onTick
  onFinish := fun status => inOrder (a.onFinish status) (b.onFinish status)
  onExecError := fun error => inOrder (a.onExecError error) (b.onExecError error)

end RelayHooks
end LeanSudo.Sys
