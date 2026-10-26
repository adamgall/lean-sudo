import LeanSudo.Sys.Exec
import LeanSudo.Helper
import LeanSudo.Sys.Prim.Edit
import LeanSudo.Sys.Prim.Posix
import LeanSudo.Sys.Prim.CoreLogs

namespace LeanSudo.Sys.Edit

open Prim.Posix

namespace P
export Prim.Edit (Packet Platform platform socketPair sendMsg recvMsg openAt accessAt
  unlinkAt stat pread pwrite truncate sync setTimes clock)
end P

namespace E
export Prim.Exec (strerror close umask waitpid)
end E

def noneFd : UInt32 := 0xFFFFFFFF

structure Identity where
  uid : UInt32
  gid : UInt32
  groups : Array UInt32

def identity (uid gid : Nat) (groups : List Nat) : IO Identity := do
  let some u := Exec.toId? uid | throw (IO.userError "invalid edit uid")
  let some g := Exec.toId? gid | throw (IO.userError "invalid edit gid")
  let gs ← groups.toArray.mapM fun n => match Exec.toId? n with
    | some v => pure v
    | none => throw (IO.userError "invalid edit group")
  pure ⟨u, g, gs⟩

structure Result where
  name : String
  value : UInt32

private def fail {α : Type} (error : UInt32) : IO α := do
  throw (IO.userError (← E.strerror error))

private def checked {α : Type} (result : Except UInt32 α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => fail error

def close (fd : UInt32) : IO Unit := do
  if fd <= INT_MAX () then
    try E.close fd catch _ => pure ()

def stat (fd : UInt32) : IO (Array Nat) := do
  if fd > INT_MAX () then fail (EBADF ())
  checked (← P.stat fd)

def authorizeFile (typeMask regular mode : Nat) (invalid : UInt32) : Except UInt32 Unit :=
  if mode &&& typeMask = regular then .ok () else .error invalid

theorem authorizeFile_regular (typeMask regular mode : Nat) (invalid : UInt32) :
    authorizeFile typeMask regular mode invalid = .ok () ↔ mode &&& typeMask = regular := by
  by_cases h : mode &&& typeMask = regular <;> simp [authorizeFile, h]

private def atDir (platform : P.Platform) (dir : UInt32) : UInt32 :=
  if dir == noneFd then platform.atFdcwd.toUInt32 else dir

private def tempChars : ByteArray :=
  "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789".toUTF8

private partial def randomBytes (count : Nat) (acc : ByteArray := .empty) : IO ByteArray := do
  if acc.size ≥ count then return acc
  let (error, bytes) ← Prim.CoreLogs.random (count - acc.size).toUInt32
  if error != 0 && error != EINTR () then fail error
  randomBytes count (acc ++ bytes)

private partial def openTemp (dir : UInt32) (front back : ByteArray) (xs : Nat) : IO Result := do
  let random ← randomBytes (2 * xs)
  let chosen := (List.range xs).foldl (fun acc i =>
    let value := random[2 * i]!.toNat + 256 * random[2 * i + 1]!.toNat
    acc.push tempChars[value % tempChars.size]!) ByteArray.empty
  let some name := String.fromUTF8? (front ++ chosen ++ back) | fail (EINVAL ())
  let flags := O_CREAT () ||| O_EXCL () ||| O_RDWR () ||| O_CLOEXEC ()
  match ← P.openAt dir name flags (S_IRUSR () ||| S_IWUSR ()) with
  | .ok fd => return ⟨name, fd⟩
  | .error error => if error == EEXIST () then openTemp dir front back xs else fail error

private def createTemp (platform : P.Platform) (path : String) (suffixLen : Nat) :
    IO Result := do
  let bytes := path.toUTF8
  if suffixLen > bytes.size then fail (EINVAL ())
  let stemEnd := bytes.size - suffixLen
  let xs := ((bytes.extract 0 stemEnd).toList.reverse.takeWhile (· == 'X'.toNat.toUInt8)).length
  if xs < 6 then fail (EINVAL ())
  openTemp (atDir platform noneFd) (bytes.extract 0 (stemEnd - xs))
    (bytes.extract stemEnd bytes.size) xs

private def executeOperation (platform : P.Platform) (op dir : UInt32)
    (path : String) (suffixLen : Nat) : IO Result := do
  let dir := atDir platform dir
  if op == 0 || op == 7 then
    let flags := O_PATH () ||| O_DIRECTORY () ||| O_CLOEXEC () |||
      (if op == 0 then O_NOFOLLOW () else 0)
    return ⟨"", ← checked (← P.openAt dir path flags 0)⟩
  if op == 1 || op == 2 || op == 6 || op == 8 || op == 9 then
    let base := if op == 6 then O_PATH ()
      else if op == 2 || op == 9 then O_WRONLY () ||| O_CREAT () else O_RDONLY ()
    let flags := base ||| O_NONBLOCK () ||| O_NOCTTY () ||| O_CLOEXEC () |||
      (if op == 1 || op == 2 then O_NOFOLLOW () else 0)
    let opened ← P.openAt dir path flags platform.createMode.toUInt32
    let fd ← match opened with
      | .error error =>
        if error == ENOENT () && (op == 1 || op == 8) then pure noneFd else fail error
      | .ok fd => pure fd
    if fd == noneFd then return ⟨"", noneFd⟩
    try
      let st ← stat fd
      checked (authorizeFile (S_IFMT ()).toNat (S_IFREG ()).toNat st[0]! (EINVAL ()))
      if op == 6 then checked (← P.accessAt dir path platform.xOk.toUInt32)
      return ⟨"", fd⟩
    catch error =>
      close fd
      throw error
  if op == 3 then
    match ← P.accessAt dir "." platform.wOk.toUInt32 with
    | .ok () => return ⟨"", 1⟩
    | .error error =>
      if error.toNat == platform.eAccess || error.toNat == platform.eReadOnly then
        return ⟨"", 0⟩
      else fail error
  else if op == 4 then
    if path.utf8ByteSize >= platform.pathMax then fail platform.eNameTooLong.toUInt32
    if suffixLen > (INT_MAX ()).toNat then fail (EINVAL ())
    createTemp platform path suffixLen
  else if op == 5 then
    match ← P.unlinkAt dir path with
    | .ok () => return ⟨"", noneFd⟩
    | .error error =>
      if error == ENOENT () then return ⟨"", noneFd⟩ else fail error
  else fail (EINVAL ())

private structure Plan where
  socket : Nat
  op : Nat
  dir : Nat
  path : String
  uid : Nat
  gid : Nat
  groups : Array Nat
  mask : Nat
  suffixLen : Nat
  deriving Lean.ToJson, Lean.FromJson

private structure Reply where
  error : Option String := none
  name : String := ""
  value : Nat := 0
  hasFd : Bool := false
  deriving Lean.ToJson, Lean.FromJson

private def wordShift (platform : P.Platform) (width index : Nat) : Nat :=
  (if platform.littleEndian == 1 then index else width - 1 - index) * 8

private def putWord (platform : P.Platform) (bytes : ByteArray)
    (offset width value : Nat) : ByteArray :=
  (List.range width).foldl
    (fun bytes i => bytes.set! (offset + i) (value >>> wordShift platform width i).toUInt8) bytes

private def getWord (platform : P.Platform) (bytes : ByteArray) (offset width : Nat) : Nat :=
  (List.range width).foldl
    (fun value i => value ||| (bytes[offset + i]!.toNat <<< wordShift platform width i)) 0

private def descriptorControl (platform : P.Platform) (fd : UInt32) : ByteArray := Id.run do
  let mut bytes : ByteArray := ⟨Array.replicate platform.cmsgSpace 0⟩
  bytes := putWord platform bytes
    platform.cmsgLengthOffset platform.cmsgLengthWidth platform.cmsgLength
  bytes := putWord platform bytes
    platform.cmsgLevelOffset platform.cmsgLevelWidth platform.solSocket
  bytes := putWord platform bytes platform.cmsgTypeOffset platform.cmsgTypeWidth platform.scmRights
  return putWord platform bytes platform.cmsgDataOffset platform.intWidth fd.toNat

private def controlLength (platform : P.Platform) (control : ByteArray) : Nat :=
  getWord platform control platform.cmsgLengthOffset platform.cmsgLengthWidth

private def rightsControl (platform : P.Platform) (control : ByteArray) : Bool :=
  getWord platform control platform.cmsgLevelOffset platform.cmsgLevelWidth == platform.solSocket &&
    getWord platform control platform.cmsgTypeOffset platform.cmsgTypeWidth == platform.scmRights

private def receivedFds (platform : P.Platform) (control : ByteArray) : Array UInt32 := Id.run do
  if control.size < platform.cmsgDataOffset || !rightsControl platform control then return #[]
  let length := min (controlLength platform control) control.size
  return ((List.range ((length - platform.cmsgDataOffset) / platform.intWidth)).toArray.map
    fun i => (getWord platform control (platform.cmsgDataOffset + platform.intWidth * i)
      platform.intWidth).toUInt32)

private def validControl (platform : P.Platform) (control : ByteArray) (hasFd : Bool) : Bool :=
  if hasFd then
    control.size == platform.cmsgSpace &&
      controlLength platform control == platform.cmsgLength && rightsControl platform control
  else control.isEmpty

private partial def sendReply (fd : UInt32) (bytes control : ByteArray) : IO Bool := do
  match ← P.sendMsg fd bytes control with
  | .error error => if error == EINTR () then sendReply fd bytes control else return false
  | .ok sent => return sent.toNat == bytes.size

private def helper (json : Lean.Json) : IO UInt32 := do
  let platform ← P.platform
  let .ok plan := (Lean.fromJson? json : Except String Plan) | return 1
  if plan.socket > (INT_MAX ()).toNat then return 1
  let socket := plan.socket.toUInt32
  let opened ← IO.mkRef noneFd
  let temp ← IO.mkRef ""
  let reply ← try
    unless plan.op < UInt32.size && plan.dir < UInt32.size &&
        (plan.dir == noneFd.toNat || plan.dir <= (INT_MAX ()).toNat) &&
        plan.uid < noneFd.toNat && plan.gid < noneFd.toNat &&
        plan.groups.size <= (INT_MAX ()).toNat && plan.groups.all (· < noneFd.toNat) &&
        Exec.cSafe plan.path && plan.mask <= platform.modeMask &&
        plan.suffixLen < UInt32.size do
      fail (EINVAL ())
    Helper.dropCredentials plan.uid.toUInt32 plan.gid.toUInt32 (plan.groups.map Nat.toUInt32)
    discard <| E.umask plan.mask.toUInt32
    let result ← executeOperation platform plan.op.toUInt32 plan.dir.toUInt32
      plan.path plan.suffixLen
    if plan.op != 3 then opened.set result.value
    if plan.op == 4 && (← opened.get) != noneFd then temp.set result.name
    pure ({
      name := result.name
      value := if plan.op == 3 then result.value.toNat else 0
      hasFd := (← opened.get) != noneFd } : Reply)
  catch error => pure ({ error := some error.toString } : Reply)
  let bytes := (Lean.toJson reply).compress.toUTF8
  let descriptor ← opened.get
  let control := if descriptor == noneFd then ByteArray.empty
    else descriptorControl platform descriptor
  let sent ← try sendReply socket bytes control catch _ => pure false
  let temporary ← temp.get
  if !sent && temporary != "" then discard <| P.unlinkAt (atDir platform noneFd) temporary
  close descriptor
  close socket
  return if sent then 0 else 1

def registerHelper : IO Unit := Helper.register "sudoedit" helper

private partial def receiveReply (fd : UInt32) : IO (Except UInt32 P.Packet) := do
  match ← P.recvMsg fd with
  | .error error => if error == EINTR () then receiveReply fd else return .error error
  | result => return result

private partial def waitHelper (pid : UInt32) : IO (Int64 × UInt32) := do
  let result ← E.waitpid pid 0
  if result.1.toInt == -Int.ofNat (EINTR ()).toNat then waitHelper pid else return result

def operation (who : Identity) (op : UInt32) (dir : UInt32 := noneFd)
    (path : String := "") (mask : Nat := (Prim.Edit.defaultMask ()).toNat)
    (suffixLen : Nat := 0) : IO Result := do
  let platform ← P.platform
  unless Exec.cSafe path && mask ≤ platform.modeMask && suffixLen < UInt32.size do
    throw (IO.userError "invalid edit path or umask")
  unless (dir == noneFd || dir <= INT_MAX ()) && who.uid != noneFd && who.gid != noneFd &&
      who.groups.size <= (INT_MAX ()).toNat && who.groups.all (· != noneFd) do fail (EINVAL ())
  let (reader, writer) ← checked (← P.socketPair)
  let plan : Plan := {
    socket := writer.toNat, op := op.toNat, dir := dir.toNat, path,
    uid := who.uid.toNat, gid := who.gid.toNat, groups := who.groups.map UInt32.toNat,
    mask, suffixLen }
  let pid ← try
    Helper.spawn "sudoedit" (Lean.toJson plan) (if dir == noneFd then #[writer] else #[writer, dir])
  catch error =>
    close reader
    close writer
    throw error
  close writer
  let packet ← try receiveReply reader finally close reader
  let (waited, status) ← waitHelper pid
  let .ok packet := packet | fail (EIO ())
  let fds := receivedFds platform packet.control
  try
    unless waited.toInt == Int.ofNat pid.toNat && status == 0 &&
        packet.flags.toNat &&& (platform.msgTrunc ||| platform.msgCtrunc) == 0 do fail (EIO ())
    let some text := String.fromUTF8? packet.bytes | fail (EIO ())
    let .ok json := Lean.Json.parse text | fail (EIO ())
    let .ok reply := (Lean.fromJson? json : Except String Reply) | fail (EIO ())
    unless validControl platform packet.control reply.hasFd &&
        fds.size == (if reply.hasFd then 1 else 0) do fail (EIO ())
    if let some error := reply.error then throw (IO.userError error)
    if op == 3 then
      unless !reply.hasFd && reply.value <= 1 do fail (EIO ())
      return ⟨reply.name, reply.value.toUInt32⟩
    return ⟨reply.name, fds[0]?.getD noneFd⟩
  catch error =>
    for fd in fds do close fd
    throw error

private partial def readContents (fd : UInt32) (size : Nat) (bytes : ByteArray) : IO ByteArray := do
  if bytes.size >= size then return bytes
  let result ← P.pread fd bytes.size.toUInt64 (min (size - bytes.size) 1048576).toUInt32
  match result with
  | .error error => if error == EINTR () then readContents fd size bytes else fail error
  | .ok chunk =>
    if chunk.isEmpty then fail (EIO ())
    readContents fd size (if bytes.isEmpty then chunk else bytes ++ chunk)

def read (fd : UInt32) : IO ByteArray := do
  let platform ← P.platform
  let before ← stat fd
  checked (authorizeFile (S_IFMT ()).toNat (S_IFREG ()).toNat before[0]! (EINVAL ()))
  let size := before[3]!
  if size > platform.maxOffset then fail (EINVAL ())
  let bytes ← readContents fd size ByteArray.empty
  let after ← P.stat fd
  match after with
  | .error _ => fail (EAGAIN ())
  | .ok after =>
    unless before[3]! == after[3]! && before[4]! == after[4]! &&
        before[5]! == after[5]! do fail (EAGAIN ())
    return bytes

private partial def replaceBytes (fd : UInt32) (bytes : ByteArray) (pos : Nat := 0) : IO Unit := do
  if pos < bytes.size then
    match ← P.pwrite fd bytes pos.toUInt64 (min (bytes.size - pos) 1048576).toUInt64 with
    | .error error => if error == EINTR () then replaceBytes fd bytes pos else fail error
    | .ok count =>
      if count == 0 then fail (EIO ())
      replaceBytes fd bytes (pos + count.toNat)
  else
    checked (← P.truncate fd bytes.size.toUInt64)
    checked (← P.sync fd)

def write (fd : UInt32) (bytes original : @& ByteArray) : IO Unit := do
  if fd > INT_MAX () then fail (EBADF ())
  try replaceBytes fd bytes catch error =>
    try replaceBytes fd original catch _ =>
      throw (IO.userError "write failed and original contents could not be restored")
    throw error

def setTimes (fd : UInt32) (seconds nanos : UInt64) : IO Unit := do
  if fd > INT_MAX () || nanos >= 1000000000 then fail (EINVAL ())
  checked (← P.setTimes fd seconds nanos)

def clock : IO UInt64 := do
  let time ← checked (← P.clock)
  return time.seconds * 1000000000 + time.nanos

end LeanSudo.Sys.Edit
