import LeanSudo.Sys.Prim.Plugins
import LeanSudo.Sys.Prim.Posix
import LeanSudo.Sys.Pam

namespace LeanSudo.Sys.Plugins.Callbacks

namespace P
export Prim.Plugins (setErrno openTty write closeFd readPtr erase length free writePtr readU32
  string dupBytes hookGet hookSet hookUnset realGet realSet realUnset realPut eventAlloc
  now poll event
  install replySize replyValue messageSize messageType messageTimeout messageText
  hookVersion hookType hookFunction hookClosure conversationVersion unsupported
  signalCount timespecGet timespecSet pollIn pollOut pollFailed)
end P

private def failure : USize := 0 - 1

structure Hook where
  kind : UInt32
  fn : USize
  closure : USize
  deriving Inhabited, BEq

structure Event where
  ptr : USize
  generation : Nat
  fd : UInt32 := 0xffffffff
  flags : UInt32 := 0
  callback : USize := 0
  closure : USize := 0
  active : Bool := false
  deadline : Nat := 0
  deriving Inhabited

structure State where
  hooks : Array Hook := #[]
  inHook : Bool := false
  events : Array Event := #[]
  nextGeneration : Nat := 0
  signals : Array UInt32 := #[]
  broken : Bool := false
  useStdin : Bool := false
  noninteractive : Bool := false
  settings : Array String := #[]
  deriving Inhabited

initialize state : IO.Ref State ← IO.mkRef {}

private def error : IO USize := do
  P.setErrno (Prim.Posix.EINVAL ())
  return failure

private def printMessage (kind : UInt32) (text size : USize) : IO USize := do
  let base := kind &&& 0xff
  if base != 3 && base != 4 then return ← error
  let tty ← if kind &&& 0x2000 != 0 then
      P.openTty (Prim.Posix.O_WRONLY () ||| Prim.Posix.O_CLOEXEC ())
    else pure 0xffffffff
  let fd := if tty != 0xffffffff then tty
    else if base == 3 then Prim.Posix.STDERR_FILENO () else Prim.Posix.STDOUT_FILENO ()
  try
    let mut written : USize := 0
    for _ in [:size.toNat + 1] do
      if written == size then return size
      let n ← P.write fd (text + written) (size - written)
      if n == failure || n == 0 then return failure
      written := written + n
    return failure
  finally
    if tty != 0xffffffff then discard <| P.closeFd tty

private def clearReplies (count : Nat) (replies : USize) : IO Unit := do
  if replies == 0 then return
  for i in [:count] do
    let value ← P.readPtr replies (i.toUSize * P.replySize () + P.replyValue ())
    if value != 0 then
      P.erase value (← P.length value)
      P.free value
      P.writePtr replies (i.toUSize * P.replySize () + P.replyValue ()) 0

private def converse (count messages replies callback : USize) : IO USize := do
  if count.toNat > (Prim.Posix.INT_MAX ()).toNat || (count != 0 && messages == 0) then
    return ← error
  for i in [:count.toNat] do
    if replies != 0 then P.writePtr replies (i.toUSize * P.replySize () + P.replyValue ()) 0
  let callback ← if callback == 0 then pure 0 else do
    let version ← P.readU32 callback (P.conversationVersion ())
    pure <| if version >>> 16 == 1 then callback else 0
  let s ← state.get
  let mut good := true
  for i in [:count.toNat] do
    if !good then break
    let ptr := messages + i.toUSize * P.messageSize ()
    let kind ← P.readU32 ptr (P.messageType ())
    let timeout ← P.readU32 ptr (P.messageTimeout ())
    let text ← P.readPtr ptr (P.messageText ())
    let base := kind &&& 0xff
    if base == 3 || base == 4 then
      let size ← if text == 0 then pure 0 else P.length text
      good := (← printMessage kind text size) != failure
    else if base == 1 || base == 2 || base == 5 then
      if replies == 0 || s.noninteractive || s.settings.contains "noninteractive=true" then
        good := false
      else
        let message ← if text == 0 then pure "" else P.string text
        let reply ← try
          pluginReadReply message kind
            (if timeout > Prim.Posix.INT_MAX () then 0 else timeout)
            (s.useStdin || s.settings.contains "read_stdin=true") callback
          catch _ => pure none
        match reply with
        | none => good := false
        | some reply =>
          let value ← P.dupBytes reply
          good := value != 0
          P.writePtr replies (i.toUSize * P.replySize () + P.replyValue ()) value
    else
      P.setErrno (Prim.Posix.EINVAL ())
      good := false
  if good then return 0
  clearReplies count.toNat replies
  return failure

private def register (ptr : USize) (add : Bool) : IO USize := do
  if ptr == 0 then return ← error
  let version ← P.readU32 ptr (P.hookVersion ())
  let kind ← P.readU32 ptr (P.hookType ())
  let fn ← P.readPtr ptr (P.hookFunction ())
  if version >>> 16 != 1 || (add && fn == 0) then return ← error
  if kind < 1 || kind > 4 then
    if add then P.setErrno (P.unsupported ())
    return 1
  let h : Hook := { kind, fn, closure := ← P.readPtr ptr (P.hookClosure ()) }
  if add then state.modify fun s => { s with hooks := #[h] ++ s.hooks }
  else
    state.modify fun s => { s with hooks := s.hooks.erase h }
  return 0

private def environment (op : UInt32) (name value overwrite : USize) : IO USize := do
  let s ← state.get
  if !s.inHook then
    state.modify fun s => { s with inHook := true }
    try
      let kind := if op == 10 then 4 else if op == 11 then 1 else if op == 12 then 2 else 3
      for h in s.hooks do
        if h.kind != kind then continue
        if op == 10 then
          let (rc, result) ← P.hookGet h.fn name h.closure
          if rc != 0 then return if rc == 1 then result else 0
        else
          let rc ← if op == 11 then P.hookSet h.fn name value overwrite.toUInt32 h.closure
            else P.hookUnset h.fn name h.closure
          if rc != 0 then return if rc == 1 then 0 else failure
    finally
      state.modify fun s => { s with inHook := false }
  if op == 10 then return ← P.realGet name
  let rc ← if op == 11 then P.realSet name value overwrite.toUInt32
    else if op == 12 then P.realUnset name else P.realPut name
  return if rc == 0xffffffff then failure else rc.toUSize

def validEvent (fd flags : UInt32) (callback : USize) (signalCount kill stop : UInt32) : Bool :=
  callback != 0 && flags &&& 0xffffffe0 == 0 &&
    (flags &&& 16 == 0 || (fd > 0 && fd < signalCount &&
      fd != kill && fd != stop && flags &&& 6 == 0))

theorem validEvent_has_callback (fd flags : UInt32) (callback : USize)
    (signalCount kill stop : UInt32)
    (h : validEvent fd flags callback signalCount kill stop = true) : callback != 0 := by
  simp only [validEvent, Bool.and_eq_true] at h
  exact h.1.1

def validEventPlan (fd flags : UInt32) (callback : USize)
    (signalCount kill stop descriptorMax : UInt32) : Bool :=
  validEvent fd flags callback signalCount kill stop &&
    (flags &&& 6 == 0 || fd ≤ descriptorMax)

theorem validEventPlan_iff (fd flags : UInt32) (callback : USize)
    (signalCount kill stop descriptorMax : UInt32) :
    validEventPlan fd flags callback signalCount kill stop descriptorMax = true ↔
      validEvent fd flags callback signalCount kill stop = true ∧
      (flags &&& 6 = 0 ∨ fd ≤ descriptorMax) := by
  simp [validEventPlan]

theorem validEventPlan_preserves_valid (fd flags : UInt32) (callback : USize)
    (signalCount kill stop descriptorMax : UInt32) (h : fd ≤ descriptorMax) :
    validEventPlan fd flags callback signalCount kill stop descriptorMax =
      validEvent fd flags callback signalCount kill stop := by
  simp [validEventPlan, h]

theorem validEventPlan_rejects_descriptor (fd flags : UInt32) (callback : USize)
    (signalCount kill stop descriptorMax : UInt32)
    (io : flags &&& 6 ≠ 0) (overflow : descriptorMax < fd) :
    validEventPlan fd flags callback signalCount kill stop descriptorMax = false := by
  simp [validEventPlan, io, UInt32.not_le.mpr overflow]

theorem validEventPlan_signal_bounds (fd flags : UInt32) (callback : USize)
    (signalCount kill stop descriptorMax : UInt32) (signal : flags &&& 16 ≠ 0)
    (h : validEventPlan fd flags callback signalCount kill stop descriptorMax = true) :
    0 < fd ∧ fd < signalCount ∧ fd ≠ kill ∧ fd ≠ stop ∧ flags &&& 6 = 0 := by
  have valid := ((validEventPlan_iff fd flags callback
    signalCount kill stop descriptorMax).mp h).1
  simp only [validEvent, Bool.and_eq_true] at valid
  simpa [signal, and_assoc] using valid.2

theorem validEventPlan_has_callback (fd flags : UInt32) (callback : USize)
    (signalCount kill stop descriptorMax : UInt32)
    (h : validEventPlan fd flags callback signalCount kill stop descriptorMax = true) :
    callback != 0 :=
  validEvent_has_callback fd flags callback signalCount kill stop
    ((validEventPlan_iff fd flags callback signalCount kill stop descriptorMax).mp h).1

private def modifyEvent (ptr : USize) (f : Event → Event) : IO Unit :=
  state.modify fun s => { s with events := s.events.map fun e => if e.ptr == ptr then f e else e }

private def eventOperation (op : UInt32) (ptr b c d e : USize) : IO USize := do
  if op == 28 then
    let ptr ← P.eventAlloc
    if ptr == 0 then return 0
    state.modify fun s => { s with
      events := #[{ ptr, generation := s.nextGeneration }] ++ s.events
      nextGeneration := s.nextGeneration + 1 }
    return ptr
  if op == 26 then
    state.modify fun s => { s with broken := true }
    return 0
  let some event := (← state.get).events.find? (·.ptr == ptr) | return ← error
  if op == 20 then
    if !validEventPlan b.toUInt32 c.toUInt32 d (P.signalCount ())
        (Prim.Posix.SIGKILL ()) (Prim.Posix.SIGSTOP ()) (Prim.Posix.INT_MAX ()) then
      return ← error
    modifyEvent ptr fun ev => { ev with
      fd := b.toUInt32
      flags := c.toUInt32
      callback := d
      closure := e
      active := false
      deadline := 0 }
    return 1
  if op == 21 then
    if event.callback == 0 then return ← error
    let now := (← P.now).toNat
    let mut deadline := 0
    if b != 0 then
      let (sec, nsec) ← P.timespecGet b
      let seconds := sec.toNat
      let nanos := nsec.toNat
      if nanos >= 1000000000 || seconds > (9223372036854775807 - now) / 1000000000 then
        return ← error
      deadline := now + seconds * 1000000000 + nanos
    modifyEvent ptr fun ev => { ev with active := true, deadline }
    return 1
  if op == 22 || op == 25 then
    if op == 25 && b != 0 then return ← error
    modifyEvent ptr fun ev => { ev with active := false }
    return 1
  if op == 23 then
    if !event.active then return 0
    let mut result := event.flags &&& b.toUInt32
    if event.deadline != 0 && b.toUInt32 &&& 1 != 0 then
      result := result ||| 1
      let left := event.deadline - (← P.now).toNat
      if c != 0 then
        P.timespecSet c (left / 1000000000).toUInt64 (left % 1000000000).toUInt64
    return result.toUSize
  if op == 24 then return event.fd.toUSize
  if op == 27 then
    state.modify fun s => { s with events := s.events.filter (·.ptr != ptr) }
    P.free ptr
    return 0
  return ← error

private def dispatch (op : UInt32) (a b c d e : USize) : IO USize := do
  if op == 0 then return ← converse a b c d
  if op == 1 then return ← printMessage a.toUInt32 b c
  if op == 2 || op == 3 then return ← register a (op == 2)
  if op >= 10 && op <= 13 then return ← environment op a b c
  return ← eventOperation op a b c d e

def install : IO Unit := P.install dispatch

def signal (signo : UInt32) : IO Unit :=
  state.modify fun s =>
    if s.events.any (fun e => e.active && e.flags &&& 16 != 0 && e.fd == signo) then
      { s with signals := s.signals.push signo }
    else s

def tick : IO Unit := do
  let snapshot ← state.get
  if snapshot.broken then throw (IO.userError "plugin event loop interrupted")
  state.modify fun s => { s with signals := #[] }
  if !snapshot.events.any (·.active) then return
  let now := (← P.now).toNat
  let mut ready : Array (Event × UInt32) := #[]
  for e in snapshot.events do
    if !e.active then continue
    let mut what : UInt32 := 0
    if e.flags &&& 16 != 0 then
      if snapshot.signals.contains e.fd then what := what ||| 16
    else if e.flags &&& 6 != 0 then
      let mask := (if e.flags &&& 2 != 0 then P.pollIn () else 0) |||
        (if e.flags &&& 4 != 0 then P.pollOut () else 0)
      let revents ← P.poll e.fd mask
      if revents &&& (P.pollIn () ||| P.pollFailed ()) != 0 then what := what ||| (e.flags &&& 2)
      if revents &&& (P.pollOut () ||| P.pollFailed ()) != 0 then what := what ||| (e.flags &&& 4)
    if e.deadline != 0 && now >= e.deadline then what := what ||| 1
    if what != 0 then ready := ready.push (e, what)
  for (e, what) in ready do
    let current ← state.get
    if current.broken then break
    if !current.events.any (fun v => v.ptr == e.ptr && v.generation == e.generation && v.active)
      then continue
    modifyEvent e.ptr fun v => { v with
      active := if v.flags &&& 8 == 0 then false else v.active
      deadline := if what &&& 1 != 0 then 0 else v.deadline }
    P.event e.callback e.fd what e.closure
  if (← state.get).broken then throw (IO.userError "plugin event loop interrupted")

def reset : IO Unit := do
  for e in (← state.get).events do P.free e.ptr
  state.set {}
  pluginConfigureConversation false ""

end LeanSudo.Sys.Plugins.Callbacks
