import LeanSudo.Sys.PluginCallbacks
import LeanSudo.Sys.PluginUserInfo
import LeanSudo.Sys.Prim.Intercept
import LeanSudo.Sys.Relay

namespace LeanSudo.Sys.Plugins

private structure Vector where
  ptr : USize := 0
  count : Nat := 0
  deriving Inhabited

private def Vector.free (v : Vector) : IO Unit := do
  for i in [:v.count] do
    Prim.Plugins.free (← Prim.Plugins.readPtr v.ptr (i.toUSize * Prim.Plugins.pointerSize ()))
  Prim.Plugins.free v.ptr

private def vector (values : Array String) : IO Vector := do
  let ptr ← Prim.Plugins.alloc ((values.size + 1).toUSize * Prim.Plugins.pointerSize ())
  if ptr == 0 then throw (IO.userError "unable to allocate plugin context")
  let v : Vector := { ptr, count := values.size }
  try
    let mut index := 0
    for value in values do
      if value.contains '\x00' then throw (IO.userError "unable to allocate plugin context")
      let item ← Prim.Plugins.dup value
      if item == 0 then throw (IO.userError "unable to allocate plugin context")
      Prim.Plugins.writePtr ptr (index.toUSize * Prim.Plugins.pointerSize ()) item
      index := index + 1
    return v
  catch e =>
    v.free
    throw e

private structure Command where
  info : Array String := #[]
  infoVec : Vector := {}
  argv : Vector := {}
  env : Vector := {}
  deriving Inhabited

private def Command.free (c : Command) : IO Unit := do
  c.infoVec.free
  c.argv.free
  c.env.free

private def command (info argv env : Array String) : IO Command := do
  let infoVec ← vector info
  let argvVec ← try vector argv catch e =>
    infoVec.free
    throw e
  let envVec ← try vector env catch e =>
    infoVec.free
    argvVec.free
    throw e
  return { info, infoVec, argv := argvVec, env := envVec }

private structure Plugin where
  handle : USize
  abi : USize
  type : UInt32
  version : UInt32
  name : String
  path : String
  line : UInt32
  options : Vector
  settings : Option Vector := none
  opened : Bool := false
  disabled : Bool := false
  disabledStreams : UInt32 := 0
  deriving Inhabited

private structure Session where
  plugins : Array (IO.Ref Plugin) := #[]
  settings : Option (Array String) := none
  userInfo : Vector := {}
  submitArgv : Vector := {}
  submitEnv : Vector := {}
  submitOptind : UInt32 := 0
  command : Command := {}
  nativeStatus : Option (UInt32 × UInt32) := none
  deriving Inhabited

private initialize session : IO.Ref Session ← IO.mkRef {}

private def method (p : Plugin) (index : Nat) : IO USize :=
  Prim.Plugins.readPtr p.abi (Prim.Plugins.methodOffset p.type index)

private def warn (message : String) : IO Unit := writeStderr ("sudo: " ++ message ++ "\n")

private def hooks (p : Plugin) (add : Bool) : IO Unit := do
  let index := if p.type == 2 && p.version >= 0x10002 then some (if add then 8 else 9)
    else if p.type == 3 then some (if add then 6 else 7) else none
  if let some index := index then
    let fn ← method p index
    if fn != 0 then Prim.Plugins.hooks fn add

private def disable (ref : IO.Ref Plugin) : IO Unit := do
  hooks (← ref.get) false
  ref.modify fun p => { p with disabled := true }

def compatibleVersion (version : UInt32) : Bool := version >>> 16 == 1

def supportedType (type : UInt32) : Bool := type >= 2 && type <= 4

theorem compatibleVersion_major (version : UInt32) (h : compatibleVersion version = true) :
    version >>> 16 = 1 := by
  simpa [compatibleVersion] using h

theorem policy_plugin_not_supported : supportedType 1 = false := by
  rfl

def loadRaw (name path : String) (line : UInt32) (options : Array String) : IO Unit := do
  Callbacks.install
  let handle ← Prim.Plugins.dlopen path
  let location := s!"error in /etc/sudo.conf, line {line} while loading plugin \"{name}\""
  if handle == 0 then
    let why ← Prim.Plugins.dlerror
    warn location
    warn s!"unable to load {path}: {why}"
    throw (IO.userError "fatal error, unable to load plugins")
  try
    let mut abi ← Prim.Plugins.dlsym handle name
    if abi == 0 then
      warn location
      warn s!"unable to find symbol \"{name}\" in {path}"
      throw (IO.userError "fatal error, unable to load plugins")
    let type ← Prim.Plugins.readU32 abi (Prim.Plugins.pluginType ())
    let mut version ← Prim.Plugins.readU32 abi (Prim.Plugins.pluginVersion ())
    if !compatibleVersion version then
      warn location
      warn s!"incompatible plugin major version {version >>> 16} (expected 1) found in {path}"
      throw (IO.userError "fatal error, unable to load plugins")
    if !supportedType type then
      warn location
      if type == 1 then
        warn s!"policy plugin {name} is not supported; policy is implemented by Lean"
      else warn s!"unknown plugin type {type} found in {path}"
      throw (IO.userError "fatal error, unable to load plugins")
    for ref in (← session.get).plugins do
      let p ← ref.get
      if p.type != type || p.name != name then continue
      let clone ← Prim.Plugins.dlsym handle (name ++ "_clone")
      let copy ← if clone == 0 then pure 0 else Prim.Plugins.clone clone
      if copy == 0 then
        warn s!"ignoring duplicate plugin \"{name}\" in /etc/sudo.conf, line {line}"
        discard <| Prim.Plugins.dlclose handle
        return
      let copyType ← Prim.Plugins.readU32 copy (Prim.Plugins.pluginType ())
      let copyVersion ← Prim.Plugins.readU32 copy (Prim.Plugins.pluginVersion ())
      if copyType != type || !compatibleVersion copyVersion then
        warn s!"incompatible cloned plugin {name}"
        throw (IO.userError "fatal error, unable to load plugins")
      abi := copy
      version := copyVersion
      break
    let options ← try
      if options.isEmpty then pure {} else vector options
      catch _ =>
        warn "unable to allocate memory"
        throw (IO.userError "fatal error, unable to load plugins")
    let p : Plugin := { handle, abi, type, version, name, path, line, options }
    if type == 2 && version >= 0x1000f then
      Prim.Plugins.eventSetter (abi + Prim.Plugins.methodOffset type 12)
    if type == 3 && version >= 0x10011 then
      Prim.Plugins.eventSetter (abi + Prim.Plugins.methodOffset type 8)
    let ref ← IO.mkRef p
    session.modify fun s => { s with plugins := s.plugins.push ref }
    hooks p true
  catch e =>
    discard <| Prim.Plugins.dlclose handle
    throw e

private def pluginSettings (ref : IO.Ref Plugin) : IO Vector := do
  let p ← ref.get
  if let some settings := p.settings then return settings
  let s ← session.get
  let intercept ← Prim.Intercept.traceSupported
  let settings ← vector <| #["plugin_path=" ++ p.path] ++ s.settings.getD #[] ++
    (if intercept then #["intercept_setid=true", "intercept_ptrace=true"] else #[])
  ref.modify fun p => { p with settings := some settings }
  return settings

private def openPlugin (ref : IO.Ref Plugin) (c : Command) (version : Bool := false) :
    IO Prim.Plugins.Result := do
  let p ← ref.get
  let settings ← try pluginSettings ref catch _ => pure {}
  if settings.ptr == 0 then return (0xffffffff, some "unable to allocate memory")
  let s ← session.get
  let fn ← method p 0
  if fn == 0 then return (0xffffffff, some "missing open method")
  if p.type == 3 || p.type == 4 then
    return ← Prim.Plugins.openCommon fn settings.ptr s.userInfo.ptr s.submitOptind
      s.submitArgv.ptr s.submitEnv.ptr p.options.ptr
  let count := if version then 0 else c.argv.count.toUInt32
  let info := if version then 0 else c.infoVec.ptr
  let argv := if version then s.submitArgv.ptr else c.argv.ptr
  let env := if version then s.submitEnv.ptr else c.env.ptr
  if p.version == 0x10000 then
    return ← Prim.Plugins.openIo0 fn settings.ptr s.userInfo.ptr count argv env
  if p.version == 0x10001 then
    return ← Prim.Plugins.openIo1 fn settings.ptr s.userInfo.ptr info count argv env
  if p.version < 0x1000f then
    return ← Prim.Plugins.openIo2 fn settings.ptr s.userInfo.ptr info count argv env p.options.ptr
  return ← Prim.Plugins.openIo fn settings.ptr s.userInfo.ptr info count argv env p.options.ptr

private def auditError (source : USize) (name : String) (type : UInt32)
    (message : String) (info : USize) : IO Bool := do
  let mut success := true
  for ref in (← session.get).plugins do
    let p ← ref.get
    if p.abi == source || p.disabled || !p.opened || p.type != 3 then continue
    let fn ← method p 4
    if fn == 0 then continue
    let (rc, why) ← Prim.Plugins.message fn name type message info
    if rc != 1 then
      warn (s!"{p.name}: unable to log error event" ++ (why.map (": " ++ ·)).getD "")
      success := false
  return success

private def auditMessage (name : String) (type : UInt32) (message : String)
    (info : USize) (isError : Bool) : IO Bool := do
  if isError then return ← auditError 0 name type message info
  for ref in (← session.get).plugins do
    let p ← ref.get
    if p.disabled || !p.opened || p.type != 3 then continue
    let fn ← method p 3
    if fn == 0 then continue
    let (rc, why) ← Prim.Plugins.message fn name type message info
    if rc != 1 then
      warn (s!"{p.name}: unable to log reject event" ++ (why.map (": " ++ ·)).getD "")
      discard <| auditError p.abi p.name 3 (why.getD "audit plugin error") info
      return false
  return true

private def auditAccept (name : String) (type : UInt32) (c : Command) : IO Bool := do
  for ref in (← session.get).plugins do
    let p ← ref.get
    if p.disabled || !p.opened || p.type != 3 then continue
    let fn ← method p 2
    if fn == 0 then continue
    let (rc, why) ← Prim.Plugins.accept fn name type c.infoVec.ptr c.argv.ptr c.env.ptr
    if rc != 1 then
      warn (s!"{p.name}: unable to log accept event" ++ (why.map (": " ++ ·)).getD "")
      discard <| auditError p.abi p.name 3 (why.getD "audit plugin error") c.infoVec.ptr
      return false
  return true

def configureConversation (useStdin nonInteractive bell : Bool) (askpass : String) : IO Unit := do
  pluginConfigureConversation bell askpass
  Callbacks.state.modify fun s => { s with useStdin, noninteractive := nonInteractive }

def openAudit (settings userInfo submitArgv submitEnv : Array String)
    (optind : UInt32) : IO Unit := do
  if (← session.get).settings.isSome then throw (IO.userError "plugins already opened")
  if optind > Prim.Posix.INT_MAX () then throw (IO.userError "invalid submit argument index")
  let context ← command userInfo submitArgv submitEnv
  session.modify fun s => { s with
    settings := some settings
    userInfo := context.infoVec
    submitArgv := context.argv
    submitEnv := context.env
    submitOptind := optind }
  Callbacks.state.modify fun s => { s with settings }
  for ref in (← session.get).plugins do
    let p ← ref.get
    if p.disabled || p.type != 3 then continue
    let (rc, _) ← openPlugin ref {}
    if rc == 0 then
      disable ref
      continue
    if rc == 0xfffffffe then throw (IO.userError "plugin requested usage")
    if rc != 1 then throw (IO.userError s!"error initializing audit plugin {p.name}")
    ref.modify fun p => { p with opened := true }

private def replaceCommand (info argv env : Array String) : IO Command := do
  let c ← command info argv env
  let old := (← session.get).command
  session.modify fun s => { s with command := c }
  old.free
  return c

def accept (commandInfo argv env : Array String) : IO Bool := do
  let c ← replaceCommand commandInfo argv env
  discard <| auditAccept "sudoers_policy" 1 c
  return true

private def checkCurrent (c : Command) (initial enforce : Bool) : IO Bool := do
  if enforce then
    let accepted ← auditAccept "sudoers_policy" 1 c
    if initial && !accepted then return false
    for ref in (← session.get).plugins do
      let p ← ref.get
      if p.disabled || p.type != 4 then continue
      let fn ← method p 2
      if fn == 0 then continue
      let (rc, _) ← openPlugin ref c
      if rc == 0 then
        disable ref
        continue
      if rc == 0xfffffffe then throw (IO.userError "plugin requested usage")
      if rc != 1 then
        warn s!"error initializing approval plugin {p.name}"
        return false
      let (result, why) ← Prim.Plugins.check fn c.infoVec.ptr c.argv.ptr c.env.ptr
      let mut result := result
      if result == 1 then
        if !(← auditAccept p.name 4 c) then result := 0xffffffff
      else if result != 0xfffffffe then
        let reason := if result == 0 then "command rejected by approver"
          else "approval plugin error"
        discard <| auditMessage p.name 4 (why.getD reason) c.infoVec.ptr (result != 0)
      let close ← method p 1
      if close != 0 then Prim.Plugins.close0 close
      if result == 0xfffffffe then throw (IO.userError "plugin requested usage")
      if result != 1 then return false
  if initial then
    for ref in (← session.get).plugins do
      let p ← ref.get
      if p.disabled || p.type != 2 then continue
      let (rc, why) ← openPlugin ref c
      if rc == 0 then
        disable ref
        continue
      if rc == 0xfffffffe then throw (IO.userError "plugin requested usage")
      if rc != 1 then
        warn s!"error initializing I/O plugin {p.name}"
        discard <| auditMessage p.name 2 (why.getD "error initializing I/O plugin")
          c.infoVec.ptr true
        return false
      ref.modify fun p => { p with opened := true }
  let accepted ← auditAccept "sudo" 0 c
  return !initial || accepted

def check (commandInfo argv env : Array String) : IO Bool := do
  checkCurrent (← replaceCommand commandInfo argv env) true true

def subcommandInfo (parent supplied : Array String) (enforce : Bool) : Array String :=
  if enforce then supplied else
    parent.filter (fun s => !s.startsWith "command=" && !s.startsWith "runcwd=") ++ supplied

theorem enforced_subcommand_info (parent supplied : Array String) :
    subcommandInfo parent supplied true = supplied := by
  rfl

def checkSubcommand (commandInfo argv env : Array String) (enforce : Bool) : IO Bool := do
  let s ← session.get
  if s.plugins.isEmpty then return true
  let c ← command (subcommandInfo s.command.info commandInfo enforce) argv env
  try checkCurrent c false enforce finally c.free

def reject (message : String) (isError : Bool) (commandInfo : Array String) : IO Unit := do
  let info ← vector commandInfo
  try
    if !(← auditMessage "sudoers_policy" 1 message info.ptr isError) then
      throw (IO.userError "unable to log policy event")
  finally info.free

def hasIo : IO Bool := do
  for ref in (← session.get).plugins do
    let p ← ref.get
    if !p.disabled && p.type == 2 then return true
  return false

def ioActive : IO Bool := do
  for ref in (← session.get).plugins do
    let p ← ref.get
    if p.opened && !p.disabled && p.type == 2 then return true
  return false

private def streamIndex (stream : UInt32) : Nat :=
  if stream == 0 then 5 else if stream == 1 then 6 else if stream == 2 then 7
  else if stream == 3 then 3 else 4

def ioStream (stream : UInt32) : IO Bool := do
  if stream > 4 then return false
  for ref in (← session.get).plugins do
    let p ← ref.get
    if p.opened && !p.disabled && p.type == 2 &&
        p.disabledStreams &&& (1 <<< stream) == 0 then
      if (← method p (streamIndex stream)) != 0 then return true
  return false

def ioWrite (stream : UInt32) (data : ByteArray) : IO Bool := do
  if stream > 4 || data.size > 4294967295 then return false
  for ref in (← session.get).plugins do
    let p ← ref.get
    if !p.opened || p.disabled || p.type != 2 ||
        p.disabledStreams &&& (1 <<< stream) != 0 then continue
    let fn ← method p (streamIndex stream)
    if fn == 0 then continue
    let (rc, why) ← if p.version < 0x1000f then Prim.Plugins.logOld fn data
      else Prim.Plugins.log fn data
    if rc == 0 || rc > Prim.Posix.INT_MAX () then
      let isError := rc != 0
      if isError then
        ref.modify fun p => { p with disabledStreams := p.disabledStreams ||| (1 <<< stream) }
      let reason := if isError then "I/O plugin error" else "command rejected by I/O plugin"
      discard <| auditMessage p.name 2 (why.getD reason) (← session.get).command.infoVec.ptr isError
      return false
  return true

private def ioEvent (suspend : Bool) (rows cols signo : UInt32) : IO Unit := do
  let mask := if suspend then 64 else 32
  for ref in (← session.get).plugins do
    let p ← ref.get
    if !p.opened || p.disabled || p.type != 2 ||
        p.version < (if suspend then 0x1000d else 0x1000c) ||
        p.disabledStreams &&& mask != 0 then continue
    let fn ← method p (if suspend then 11 else 10)
    if fn == 0 then continue
    let (rc, why) ← if suspend then
        if p.version < 0x1000f then pure (← Prim.Plugins.callInt fn signo, none)
        else Prim.Plugins.suspend fn signo
      else if p.version < 0x1000f then pure (← Prim.Plugins.windowOld fn rows cols, none)
        else Prim.Plugins.window fn rows cols
    if rc == 0 || rc > Prim.Posix.INT_MAX () then
      ref.modify fun p => { p with disabledStreams := p.disabledStreams ||| mask }
      let reason := if suspend then "error logging suspend" else "error changing window size"
      discard <| auditMessage p.name 2 (why.getD reason) (← session.get).command.infoVec.ptr true
      throw (IO.userError "I/O plugin error")

def execBegin : IO Unit := session.modify fun s => { s with nativeStatus := some (3, 1) }

def execStatus (type status : UInt32) : IO Unit :=
  session.modify fun s =>
    if type == 3 && s.nativeStatus.any (fun v => v.1 == 1 || v.1 == 2) then s
    else { s with nativeStatus := some (type, status) }

def relayHooks : RelayHooks := {
  onStream := ioWrite
  needsStream := ioStream
  forcePty := ioActive
  onWindow := fun rows cols => ioEvent false rows cols 0
  onSuspend := fun signo => ioEvent true 0 0 signo
  onSignal := Callbacks.signal
  onTick := Callbacks.tick
  onExecError := execStatus 2
  onFinish := fun status => execStatus 1 status }

def showVersion (verbose : Bool) (builtinIoLine builtinAuditLine : UInt32) : IO Unit := do
  let mut builtinIo := builtinIoLine
  let mut builtinAudit := builtinAuditLine
  for type in [2, 4] do
    for ref in (← session.get).plugins do
      let p ← ref.get
      if p.disabled || p.type != type then continue
      if type == 2 && builtinIo != 0 && builtinIo < p.line then
        IO.print "Sudoers I/O plugin version 1.9.17p2\n"
        builtinIo := 0
      let showFn ← method p (if type == 2 then 2 else 3)
      if type == 4 && showFn == 0 then continue
      let (rc, _) ← openPlugin ref {} true
      let close ← method p 1
      if type == 2 then
        if rc != 0xffffffff then
          if showFn != 0 then discard <| Prim.Plugins.callInt showFn (if verbose then 1 else 0)
          if p.version >= 0x1000f && close != 0 then Prim.Plugins.close close 0 0
      else if rc == 0 then disable ref
      else if rc == 1 then
        discard <| Prim.Plugins.callInt showFn (if verbose then 1 else 0)
        if close != 0 then Prim.Plugins.close0 close
      else if rc == 0xfffffffe then throw (IO.userError "plugin requested usage")
      else throw (IO.userError "error initializing approval plugin")
    if type == 2 && builtinIo != 0 then
      IO.print "Sudoers I/O plugin version 1.9.17p2\n"
      builtinIo := 0
  for ref in (← session.get).plugins do
    let p ← ref.get
    if p.disabled || !p.opened || p.type != 3 then continue
    if builtinAudit != 0 && builtinAudit < p.line then
      IO.print "Sudoers audit plugin version 1.9.17p2\n"
      builtinAudit := 0
    let showFn ← method p 5
    if showFn != 0 then discard <| Prim.Plugins.callInt showFn (if verbose then 1 else 0)
    let close ← method p 1
    if close != 0 then Prim.Plugins.close close 0 0
    ref.modify fun p => { p with opened := false }
  if builtinAudit != 0 then IO.print "Sudoers audit plugin version 1.9.17p2\n"

def close (statusType status : UInt32) : IO Unit := do
  let s ← session.get
  let (type, status) := s.nativeStatus.getD (statusType, status)
  for ref in s.plugins do
    let p ← ref.get
    if p.opened && p.type == 2 then
      let fn ← method p 1
      if fn != 0 then
        Prim.Plugins.close fn (if type == 1 then status else 0) (if type == 2 then status else 0)
      ref.modify fun p => { p with opened := false }
  for ref in s.plugins do
    let p ← ref.get
    if p.opened && p.type == 3 then
      let fn ← method p 1
      if fn != 0 then Prim.Plugins.close fn type status
    if !p.disabled then hooks p false
  Callbacks.reset
  for ref in s.plugins do
    let p ← ref.get
    if let some settings := p.settings then settings.free
    p.options.free
    discard <| Prim.Plugins.dlclose p.handle
  s.userInfo.free
  s.submitArgv.free
  s.submitEnv.free
  s.command.free
  session.set {}

end LeanSudo.Sys.Plugins
