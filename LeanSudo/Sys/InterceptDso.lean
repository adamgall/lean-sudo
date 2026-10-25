import LeanSudo.Intercept.Protocol
import LeanSudo.Sys.InterceptTrace

namespace LeanSudo.Sys.InterceptDso

open LeanSudo.Intercept
open InterceptTrace (failure decode readBytes)
open Prim.Posix

abbrev Request := InterceptTrace.Request

namespace P
export Prim.Intercept
  (openFile close read send socket socketpair bind sockname listen accept fcntl sockopt poll
   inet stream tcp noDelay pollIn pollOut pollError pollInvalid pollHangup setidBits
   addressSize familyOffset familyWidth portOffset portWidth addressOffset addressWidth loopback)
end P

inductive Phase where
  | token
  | policy
  | hello
  | response
  deriving BEq

structure Client where
  fd : UInt32
  phase : Phase
  buffer : ByteArray := ByteArray.empty
  header : ByteArray := ByteArray.empty
  length : Nat := 0
  used : Nat := 0
  closeAfter : Bool := false

structure State where
  listener : UInt32
  child : UInt32
  port : Nat
  token : ByteArray
  logOnly : Bool
  clients : Array Client
  childClosed : Bool := false

private def flags (fd : UInt32) (nonblocking : Bool) : IO Unit := do
  let old ← P.fcntl fd (F_GETFD ()) 0
  let _ ← P.fcntl fd (F_SETFD ()) (old ||| FD_CLOEXEC ())
  if nonblocking then
    let old ← P.fcntl fd (F_GETFL ()) 0
    let _ ← P.fcntl fd (F_SETFL ()) (old ||| O_NONBLOCK ())

private def randomToken : IO ByteArray := do
  let fd ← P.openFile "/dev/urandom" (O_RDONLY () ||| O_CLOEXEC ())
  try
    for _ in [:1024] do
      let mut bytes := ByteArray.empty
      for _ in [:16] do
        if bytes.size = 16 then break
        let chunk ← readBytes fd (16 - bytes.size)
        if chunk.isEmpty then failure
        bytes := bytes ++ chunk
      if bytes.size = 16 && bytes.data.any (· ≠ 0) then return bytes
    failure
  finally P.close fd

def close (state : State) : IO Unit := do
  if !state.childClosed then
    try P.close state.child catch _ => pure ()
  try P.close state.listener catch _ => pure ()
  for client in state.clients do
    try P.close client.fd catch _ => pure ()

def parent (ref : IO.Ref State) : IO Unit := do
  let state ← ref.get
  if !state.childClosed then
    P.close state.child
    ref.set { state with childClosed := true }

private def bootstrap : IO (UInt32 × UInt32) := do
  let (parent, child) ← P.socketpair
  let inherited ← try
    flags parent true
    flags child false
    P.fcntl child (F_DUPFD_CLOEXEC ()) 64
  catch error =>
    try P.close parent catch _ => pure ()
    try P.close child catch _ => pure ()
    throw error
  try P.close child catch _ => pure ()
  return (parent, inherited)

private def loopbackBytes (_ : Unit) : ByteArray :=
  ⟨(Seccomp.little (P.addressWidth ()) (P.loopback ()).toNat).reverse.toArray⟩

private def listenAddress (_ : Unit) : ByteArray := Id.run do
  let bytes : ByteArray := ⟨Array.replicate (P.addressSize ()) 0⟩
  let mut bytes := Registers.putWord bytes (P.familyOffset ())
    (P.familyWidth ()) (P.inet ()).toNat
  let address := loopbackBytes ()
  for i in [:address.size] do
    bytes := bytes.set! (P.addressOffset () + i) (address[i]?.getD 0)
  return bytes

def prepare (logOnly : Bool) : IO State := do
  let some image ← stat "/usr/libexec/sudo/sudo_intercept.so" | failure
  if !image.isReg then failure
  let token ← randomToken
  let listener ← P.socket (P.inet ()) (P.stream ())
  try
    flags listener true
    P.bind listener (listenAddress ())
    let address ← P.sockname listener
    let port := (address.extract (P.portOffset ()) (P.portOffset () + P.portWidth ())).data.foldl
      (fun value byte => value * 256 + byte.toNat) 0
    if port = 0 then failure
    P.listen listener
    let (parent, child) ← bootstrap
    return { listener, child, token, port, logOnly
             clients := #[{ fd := parent, phase := .hello }] }
  catch error =>
    try P.close listener catch _ => pure ()
    throw error

def environment (state : State) (env : Array String) : Array String := Id.run do
  let mut preload := "LD_PRELOAD=/usr/libexec/sudo/sudo_intercept.so"
  let mut rest := #[]
  for value in env do
    if value.startsWith "LD_PRELOAD=" then
      let existing := (value.drop 11).toString
      if !existing.isEmpty then preload := preload ++ ":" ++ existing
    else if !value.startsWith "SUDO_INTERCEPT_FD=" then rest := rest.push value
  return #[preload, s!"SUDO_INTERCEPT_FD={state.child}"] ++ rest

private def receive (fd : UInt32) (bytes : ByteArray) (length : Nat) :
    IO (ByteArray × Bool) := do
  let mut bytes := bytes
  for _ in [:length + 1024] do
    if bytes.size = length then return (bytes, true)
    if bytes.size > length then failure
    let (error, chunk) ← P.read fd (length - bytes.size).toUInt32
    if error = EINTR () then continue
    if error = EAGAIN () then return (bytes, false)
    if error ≠ 0 || chunk.isEmpty then failure
    bytes := bytes ++ chunk
  failure

private def requestStat (req : Protocol.Request) : IO (Option FileStat) := do
  if req.command.startsWith "/" then return ← stat req.command
  if req.cwd.isEmpty then failure
  let directory ← P.openFile req.cwd (O_RDONLY () ||| O_DIRECTORY () ||| O_CLOEXEC ())
  try stat s!"/proc/self/fd/{directory}/{req.command}"
  finally P.close directory

private def checkRequest (check : Request → IO Bool) (req : Protocol.Request) : IO Int := do
  try
    let some image ← requestStat req | return -1
    let request : Request := {
      command := req.command, cwd := req.cwd, argv := req.argv
      env := req.env, pid := 0, setid := image.mode &&& P.setidBits () ≠ 0 }
    return if (← check request) then 1 else 0
  catch _ => return -1

private def dispatch (state : State) (check : Request → IO Bool) (client : Client) :
    IO Client := do
  if client.phase == .hello then
    if !Protocol.hello client.buffer then failure
    let some response := Protocol.helloResponse state.token state.port state.logOnly | failure
    return { client with
      phase := .response, buffer := response, length := response.size
      used := 0, closeAfter := true }
  if client.phase != .policy then failure
  let some request := Protocol.policy client.buffer | failure
  let result ← checkRequest check request
  if state.logOnly then
    if result ≠ 1 then failure
    return { fd := client.fd, phase := .hello }
  let some response := Protocol.policyResponse request result | failure
  return { client with
    phase := .response, buffer := response, length := response.size
    used := 0, closeAfter := result ≠ 1 }

private def readClient (state : State) (check : Request → IO Bool) (client : Client) :
    IO Client := do
  let mut client := client
  if client.phase == .token then
    let (secret, complete) ← receive client.fd client.buffer 16
    client := { client with buffer := secret }
    if !complete then return client
    if !Protocol.tokenMatches state.token secret then failure
    client := { fd := client.fd, phase := .policy }
  let (header, complete) ← receive client.fd client.header 4
  client := { client with header }
  if !complete then return client
  let length := Registers.word header 0 4
  if length = 0 || length > 2097152 then failure
  let (bytes, complete) ← receive client.fd client.buffer length
  client := { client with buffer := bytes, length }
  if !complete then return client
  dispatch state check client

private def writeClient (client : Client) : IO Client := do
  let mut used := client.used
  for _ in [:client.length + 1024] do
    if used = client.length then
      if client.closeAfter then failure
      return { fd := client.fd, phase := .hello }
    let result ← P.send client.fd client.buffer used.toUInt32
    if result = -(EINTR ()).toNat.toInt64 then continue
    if result = -(EAGAIN ()).toNat.toInt64 then return { client with used }
    if result ≤ 0 then failure
    used := used + result.toInt.toNat
  failure

private def accepted (fd : UInt32) (address : ByteArray) : IO (Option Client) := do
  try
    if address.size < P.addressSize () ||
        Registers.word address (P.familyOffset ()) (P.familyWidth ()) ≠ (P.inet ()).toNat ||
        address.extract (P.addressOffset ()) (P.addressOffset () + P.addressWidth ()) ≠
          loopbackBytes () then failure
    flags fd true
    P.sockopt fd (P.tcp ()) (P.noDelay ()) 1
    return some { fd, phase := .token }
  catch _ =>
    try P.close fd catch _ => pure ()
    return none

private def acceptClient (state : State) : IO (Option Client) := do
  try
    let (fd, address) ← P.accept state.listener
    accepted fd address
  catch _ => return none

def service (ref : IO.Ref State) (check : Request → IO Bool) : IO Unit := do
  let state ← ref.get
  let mut clients := #[]
  for client in state.clients do
    let next ← try
      let events ← P.poll client.fd
        (if client.phase == .response then P.pollOut () else P.pollIn ())
      if events &&& (P.pollError () ||| P.pollInvalid ()) ≠ 0 then failure
      let client ← if events &&& (P.pollIn () ||| P.pollOut () ||| P.pollHangup ()) = 0 then
          pure client
        else if client.phase == .response then writeClient client
        else readClient state check client
      pure (some client)
    catch _ =>
      try P.close client.fd catch _ => pure ()
      pure none
    if let some client := next then clients := clients.push client
  ref.set { state with clients }
  let events ← P.poll state.listener (P.pollIn ())
  if events &&& (P.pollError () ||| P.pollHangup () ||| P.pollInvalid ()) ≠ 0 then failure
  if events &&& P.pollIn () ≠ 0 then
    if let some client ← acceptClient state then clients := clients.push client
  ref.set { state with clients }

end LeanSudo.Sys.InterceptDso
