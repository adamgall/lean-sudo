import LeanSudo.LogSrv
import LeanSudo.EventLog
import LeanSudo.IoLog
import LeanSudo.Sys.Core
import LeanSudo.Sys.Extra
import LeanSudo.Sys.Prim.LogSrv
import LeanSudo.Helper

namespace LeanSudo.Sys.LogSrv
open LeanSudo.LogSrv

private abbrev NetM := EIO UInt32
namespace Prim
export LeanSudo.Sys.Prim.LogSrv (Result clock errorText resolve address freeAddresses socketpair
  socket fcntl keepalive connect socketError close poll send recv peer numeric sigpending
  sigemptyset sigaddset sigismember sigtimedwait openLibrary symbol closeLibrary
  ptr0 ptr1 ulong0 void0 void1 int1 long1 int2 ctrl
  verify ca cert key sni tlsConnect tlsSend tlsRecv certHost certIp certExt reason)
end Prim

namespace K
export LeanSudo.Sys.Prim.LogSrv.Constants (eintr eio etimedout ebadf enodata eproto enotconn
  eagain ewouldblock emsgsize epipe ehostunreach einprogress ealready enosys eacces
  eafnosupport einval getfd setfd cloexec getfl setfl nonblock pollin pollout pollnval
  pollerr pollhup inet inet6 unspec stream tcp sigpipe sockaddrStorageSize sigkill intMax
  ipv4Offset ipv4Size
  sockaddr4Size ipv6Offset ipv6Size sockaddr6Size sslWantRead sslWantWrite sslSyscall
  sslZeroReturn noPartialWildcards neverCheckSubject minProtoVersion tls12 verifyPeer verifyNone)
end K

private structure Transport where
  fd : Option UInt32 := none
  timeout : UInt32 := 0
  streams : UInt32 := 0
  cryptoLibrary : UInt64 := 0
  sslLibrary : UInt64 := 0
  api : Array UInt64 := #[]
  ctx : UInt64 := 0
  ssl : UInt64 := 0
  pipeMask : ByteArray := ByteArray.empty
  tlsErrno : UInt32 := 0
  nativeErrno : UInt32 := 0
  deriving Inhabited

private structure Frame where
  header : ByteArray := ByteArray.empty
  headerUsed : Nat := 0
  body : ByteArray := ByteArray.empty
  bodyUsed : Nat := 0
  bodyAllocated : Bool := false
  deriving Inhabited

private initialize transport : IO.Ref Transport ← IO.mkRef {}
private initialize incoming : IO.Ref Frame ← IO.mkRef {}
private initialize pendingMessages : IO.Ref (Array ByteArray) ← IO.mkRef #[]
private initialize broker : IO.Ref Bool ← IO.mkRef false

def withBroker (action : IO α) : IO α := do
  let previous ← broker.get
  broker.set true
  try action finally broker.set previous

private def checked (result : Prim.Result α) : NetM α :=
  if result.1 == 0 then pure result.2 else throw result.1

private partial def clockNanos : NetM Nat := do
  let (error, seconds, nanos) ← Prim.clock
  if error == K.eintr () then return ← clockNanos
  if error != 0 then throw error
  let seconds := seconds.toNat
  let nanos := nanos.toNat
  if nanos >= 1000000000 || seconds > (18446744073709551615 - nanos) / 1000000000 then
    throw (K.eio ())
  return seconds * 1000000000 + nanos

private def awakeTime : IO Nat := do
  match ← clockNanos.toBaseIO with
  | .ok value => return value
  | .error _ => throw (IO.userError "unable to read log server monotonic clock")

private def remaining (deadline : Nat) : NetM Nat := do
  return min (K.intMax ()).toNat (deadline - (← clockNanos) / 1000000)

private def deadlineNew (timeout : UInt32) : NetM Nat := do
  return (← clockNanos) / 1000000 + timeout.toNat * 1000

private partial def waitFd (fd events : UInt32) (wait : Bool) (deadline : Nat) : NetM Bool := do
  let ms ← remaining deadline
  if wait && ms == 0 then throw (K.etimedout ())
  let (error, revents) ← Prim.poll fd events (if wait then ms.toUInt32 else 0)
  if error == K.eintr () then
    if !wait then return false
    return ← waitFd fd events wait deadline
  if error != 0 then throw error
  if revents == 0 then
    if !wait then return false
    return ← waitFd fd events wait deadline
  if revents &&& K.pollnval () != 0 then throw (K.ebadf ())
  if revents &&& (events ||| K.pollerr () ||| K.pollhup ()) != 0 then return true
  waitFd fd events wait deadline

private def reset : BaseIO Unit := do
  let c ← transport.get
  transport.set {}
  incoming.set {}
  if c.ssl != 0 then Prim.void1 c.api[11]! c.ssl
  if c.ctx != 0 then Prim.void1 c.api[2]! c.ctx
  for fd in c.fd do discard <| Prim.close fd
  if c.sslLibrary != 0 then discard <| Prim.closeLibrary c.sslLibrary
  if c.cryptoLibrary != 0 then discard <| Prim.closeLibrary c.cryptoLibrary

private def closeTransport : IO Unit := reset

private def transportFailure (operation : String) (error : UInt32) : IO α := do
  reset
  if error == K.enodata () && operation == "receive" then
    throw (IO.userError "lost connection to log server")
  let message ← Prim.errorText (if error == 0 then K.eio () else error)
  throw (IO.userError s!"log server {operation}: {message}")

private def runNet (operation : String) (action : NetM α) : IO α := do
  match ← action.toBaseIO with
  | .ok value => return value
  | .error error => transportFailure operation error

private def nonblocking (fd : UInt32) : NetM Unit := do
  let flags ← checked (← Prim.fcntl fd (K.getfd ()) 0)
  let _ ← checked (← Prim.fcntl fd (K.setfd ()) (flags ||| K.cloexec ()))
  let flags ← checked (← Prim.fcntl fd (K.getfl ()) 0)
  discard <| checked (← Prim.fcntl fd (K.setfl ()) (flags ||| K.nonblock ()))

private def word (value : Nat) : ByteArray :=
  ByteArray.mk #[(value / 16777216).toUInt8, (value / 65536).toUInt8,
    (value / 256).toUInt8, value.toUInt8]

private def wordAt (bytes : ByteArray) (offset : Nat) : Nat :=
  bytes[offset]!.toNat * 16777216 + bytes[offset + 1]!.toNat * 65536 +
    bytes[offset + 2]!.toNat * 256 + bytes[offset + 3]!.toNat

private def pipePending : NetM Bool := do
  let pending ← checked (← Prim.sigpending)
  return (← checked (← Prim.sigismember pending (K.sigpipe ()))) != 0

private def tlsStep (c : Transport) (action : BaseIO (UInt32 × UInt32 × ByteArray)) :
    NetM (Nat × UInt32 × ByteArray) := do
  let hadPending ← pipePending
  Prim.void0 c.api[24]!
  let (saved, rc, bytes) ← action
  transport.modify fun state => { state with tlsErrno := saved }
  let positive := rc != 0 && rc <= K.intMax ()
  let error : UInt32 ← if positive then pure 0 else do
    let (_, error) ← Prim.int2 c.api[19]! c.ssl rc saved
    pure error
  if !hadPending then
    match ← pipePending.toBaseIO with
    | .ok true => discard <| Prim.sigtimedwait c.pipeMask 0
    | _ => pure ()
  if positive then return (rc.toNat, 0, bytes)
  if error == K.sslWantRead || error == K.sslWantWrite then
    return (0, if error == K.sslWantRead then K.pollin () else K.pollout (), bytes)
  if error == K.sslSyscall && saved == K.eintr () then return (0, 0, bytes)
  throw (if error == K.sslZeroReturn then K.enodata ()
    else if error == K.sslSyscall && saved != 0 then saved else K.eproto ())

private partial def transfer (c : Transport) (bytes : ByteArray) (offset count : Nat)
    (writing wait : Bool) (deadline : Nat) : NetM (Nat × ByteArray) := do
  if offset > bytes.size || count > bytes.size - offset then throw (K.einval ())
  if c.ssl != 0 && count > (K.intMax ()).toNat then throw (K.einval ())
  let some fd := c.fd | throw (K.enotconn ())
  let ms ← remaining deadline
  if ms == 0 && wait then throw (K.etimedout ())
  let (size, want, bytes) ← if c.ssl != 0 then
      tlsStep c (if writing then do
          let (error, rc) ← Prim.tlsSend c.api[18]! c.ssl bytes offset.toUSize count.toUSize
          pure (error, rc, bytes)
        else Prim.tlsRecv c.api[17]! c.ssl bytes offset.toUSize count.toUSize)
    else do
      let (error, rc, bytes) ← if writing then do
          let (error, rc) ← Prim.send fd bytes offset.toUSize count.toUSize
          pure (error, rc, bytes)
        else Prim.recv fd bytes offset.toUSize count.toUSize
      if error == 0 then
        if rc == 0 then throw (K.enodata ())
        pure (rc.toNat, 0, bytes)
      else if error == K.eintr () then pure (0, 0, bytes)
      else if error == K.eagain () || error == K.ewouldblock () then
        pure (0, if writing then K.pollout () else K.pollin (), bytes)
      else throw error
  if size != 0 then return (size, bytes)
  if want == 0 then
    if !wait || ms == 0 then return (0, bytes)
    return ← transfer c bytes offset count writing wait deadline
  if !(← waitFd fd want wait deadline) then return (0, bytes)
  if !wait && ms == 0 then return (0, bytes)
  transfer c bytes offset count writing wait deadline

private partial def writePart (c : Transport) (bytes : ByteArray) (used deadline : Nat) :
    NetM Unit := do
  if used >= bytes.size then return
  let (count, bytes) ← transfer c bytes used (bytes.size - used) true true deadline
  writePart c bytes (used + count) deadline

private partial def readPart (c : Transport) (bytes : ByteArray) (used : Nat)
    (wait : Bool) (deadline : Nat) : NetM (ByteArray × Nat) := do
  if used >= bytes.size then return (bytes, used)
  let (count, bytes) ← transfer c bytes used (bytes.size - used) false wait deadline
  if count == 0 then return (bytes, used)
  readPart c bytes (used + count) wait deadline

private def readFrame (c : Transport) (frame : Frame) (wait : Bool) (deadline : Nat) :
    NetM (Frame × Option ByteArray) := do
  let ⟨header, headerUsed, body, bodyUsed, bodyAllocated⟩ := frame
  let header := if header.isEmpty then ByteArray.mk (Array.replicate 4 0) else header
  let (header, headerUsed) ← readPart c header headerUsed wait deadline
  if headerUsed != 4 then return ({ header, headerUsed, body, bodyUsed, bodyAllocated }, none)
  let length := wordAt header 0
  if length > 2097152 then throw (K.emsgsize ())
  let body := if bodyAllocated then body else ByteArray.mk (Array.replicate length 0)
  let (body, bodyUsed) ← readPart c body bodyUsed wait deadline
  if bodyUsed != length then
    return ({ header, headerUsed, body, bodyUsed, bodyAllocated := true }, none)
  return ({}, some body)

private def send (bytes : ByteArray) : IO Unit := do
  let c ← transport.get
  if c.fd.isNone then transportFailure "send" (K.enotconn ())
  if bytes.size > 2097152 then transportFailure "send" (K.emsgsize ())
  let deadline ← runNet "clock" (deadlineNew c.timeout)
  runNet "send" do
    writePart c (word bytes.size) 0 deadline
    writePart c bytes 0 deadline

private def receive (wait : Bool) : IO (Option ByteArray) := do
  let c ← transport.get
  if c.fd.isNone then transportFailure "receive" (K.enotconn ())
  let deadline ← runNet "clock" (deadlineNew c.timeout)
  let frame ← incoming.modifyGet fun frame => (frame, {})
  let (frame, result) ← runNet "receive" (readFrame c frame wait deadline)
  incoming.set frame
  return result

private structure Address where
  family : UInt32
  kind : UInt32
  protocol : UInt32
  bytes : ByteArray

private partial def resolverWrite (fd : UInt32) (bytes : ByteArray) (used : Nat := 0) :
    NetM Unit := do
  if used == bytes.size then return
  let (error, size) ← Prim.send fd bytes used.toUSize (bytes.size - used).toUSize
  if error == K.eintr () then return ← resolverWrite fd bytes used
  if error != 0 then throw error
  if size == 0 then throw (K.epipe ())
  resolverWrite fd bytes (used + size.toNat)

private partial def resolverNodes (fd : UInt32) (node : UInt64) : NetM Unit := do
  if node == 0 then
    resolverWrite fd (word 0)
    return
  let (next, family, kind, protocol, length, bytes) ← Prim.address node
  if (family == K.inet () || family == K.inet6 ()) && length <= K.sockaddrStorageSize () then
    let header := word (12 + bytes.size) ++ word family.toNat ++
      word kind.toNat ++ word protocol.toNat
    resolverWrite fd header
    resolverWrite fd bytes
  resolverNodes fd next

def resolverHelper (payload : Lean.Json) : IO UInt32 := do
  let host ← IO.ofExcept (payload.getObjValAs? String "host")
  let service ← IO.ofExcept (payload.getObjValAs? String "service")
  let fd ← IO.ofExcept (payload.getObjValAs? Nat "fd")
  let (error, node) ← Prim.resolve host service (K.unspec ()) (K.stream ()) (K.tcp ())
  if error != 0 then return 1
  try
    match ← (resolverNodes fd.toUInt32 node).toBaseIO with
    | .ok _ => return 0
    | .error _ => return 1
  finally
    if node != 0 then Prim.freeAddresses node
    discard <| Prim.close fd.toUInt32

private partial def resolverRead (fd : UInt32) (deadline : Nat)
    (addresses : Array Address := #[]) : NetM (Array Address) := do
  let (_, some bytes) ← readFrame { fd := some fd } {} true deadline |
    throw (K.ehostunreach ())
  if bytes.isEmpty then
    if addresses.isEmpty then throw (K.ehostunreach ())
    return addresses
  if bytes.size < 12 then throw (K.ehostunreach ())
  let address : Address := {
    family := (wordAt bytes 0).toUInt32
    kind := (wordAt bytes 4).toUInt32
    protocol := (wordAt bytes 8).toUInt32
    bytes := bytes.extract 12 bytes.size }
  resolverRead fd deadline (addresses.push address)

private partial def reapResolver (pid : UInt32) : IO Unit := do
  let (result, _) ← LeanSudo.Sys.Prim.Exec.waitpid pid 0
  if result.toInt == -(Int.ofNat (K.eintr ()).toNat) then reapResolver pid

private def startResolver (host service : String) (reader writer : UInt32) : IO UInt32 := do
  try
    runNet "resolve" do
      nonblocking reader
      let flags ← checked (← Prim.fcntl writer (K.getfd ()) 0)
      discard <| checked (← Prim.fcntl writer (K.setfd ()) (flags ||| K.cloexec ()))
    LeanSudo.Helper.spawn "logsrv-resolve" (Lean.Json.mkObj [
      ("host", Lean.toJson host), ("service", Lean.toJson service),
      ("fd", Lean.toJson writer.toNat)]) #[writer]
  finally discard <| Prim.close writer

private def readResolver (pid reader : UInt32) (deadline : Nat) : IO (Array Address) := do
  let action : NetM (Array Address) := do
    try resolverRead reader deadline
    catch error => throw (if error == K.enodata () then K.ehostunreach () else error)
  try runNet "resolve" action
  finally
    let _ ← LeanSudo.Sys.Prim.Exec.kill pid (K.sigkill ())
    reapResolver pid

private def resolve (host service : String) (deadline : Nat) : IO (Array Address) := do
  let (reader, writer) ← runNet "resolve" (checked (← Prim.socketpair))
  try
    let pid ← startResolver host service reader writer
    readResolver pid reader deadline
  finally discard <| Prim.close reader

private def connectAddresses (addresses : Array Address) (keepalive : Bool) (deadline : Nat) :
    NetM Unit := do
  let mut lastError : UInt32 := K.ehostunreach ()
  for address in addresses do
    if (← remaining deadline) == 0 then throw (K.etimedout ())
    let (error, fd) ← Prim.socket address.family address.kind address.protocol
    if error != 0 then
      lastError := error
      continue
    try
      nonblocking fd
      let _ ← checked (← Prim.keepalive fd keepalive)
      let (error, _) ← Prim.connect fd address.bytes
      if error == K.einprogress () || error == K.eintr () || error == K.ealready () then
        let _ ← waitFd fd (K.pollout ()) true deadline
        let error ← checked (← Prim.socketError fd)
        if error != 0 then throw error
      else if error != 0 then throw error
      transport.modify fun c => { c with fd := some fd }
      return
    catch error =>
      lastError := error
      discard <| Prim.close fd
  throw lastError

private def tlsLoad : NetM Unit := do
  let cryptoLibrary ← Prim.openLibrary "libcrypto.so.3"
  transport.modify fun c => { c with cryptoLibrary }
  let sslLibrary ← Prim.openLibrary "libssl.so.3"
  transport.modify fun c => { c with sslLibrary }
  if cryptoLibrary == 0 || sslLibrary == 0 then throw (K.enosys ())
  let names := #["TLS_client_method", "SSL_CTX_new", "SSL_CTX_free", "SSL_CTX_ctrl",
    "SSL_CTX_set_verify", "SSL_CTX_load_verify_locations", "SSL_CTX_set_default_verify_paths",
    "SSL_CTX_use_certificate_chain_file", "SSL_CTX_use_PrivateKey_file",
    "SSL_CTX_check_private_key",
    "SSL_new", "SSL_free", "SSL_set_fd", "SSL_ctrl", "SSL_get1_peer_certificate",
    "SSL_get_verify_result", "SSL_connect", "SSL_read", "SSL_write", "SSL_get_error",
    "X509_check_host", "X509_check_ip", "X509_get_ext_by_NID", "X509_free",
    "ERR_clear_error", "ERR_get_error", "ERR_reason_error_string"]
  for index in [:names.size] do
    let fn ← Prim.symbol (if index >= 20 then cryptoLibrary else sslLibrary) names[index]!
    if fn == 0 then throw (K.enosys ())
    transport.modify fun c => { c with api := c.api.push fn }

private def tlsIdentity (host : String) : NetM Unit := do
  let c ← transport.get
  let some fd := c.fd | throw (K.enotconn ())
  let (family, peer) ← checked (← Prim.peer fd)
  let address ← if family == K.inet () && peer.size >= (K.sockaddr4Size ()).toNat then
      let offset := (K.ipv4Offset ()).toNat
      pure (peer.extract offset (offset + (K.ipv4Size ()).toNat))
    else if family == K.inet6 () && peer.size >= (K.sockaddr6Size ()).toNat then
      let offset := (K.ipv6Offset ()).toNat
      pure (peer.extract offset (offset + (K.ipv6Size ()).toNat))
    else throw (K.eafnosupport ())
  let (_, cert) ← Prim.ptr1 c.api[14]! c.ssl 0
  if cert == 0 then throw (K.eacces ())
  try
    let hostLength := host.utf8ByteSize - (if host.endsWith "." then 1 else 0)
    let extension ← Prim.certExt c.api[22]! cert
    let flags := if extension <= K.intMax () then
      K.noPartialWildcards ||| K.neverCheckSubject else K.noPartialWildcards
    let mut matched : UInt32 ← if hostLength == 0 then pure 4294967295
      else do
        let result ← Prim.certHost c.api[20]! cert host hostLength.toUSize flags
        pure result
    if matched == 0 then matched ← Prim.certIp c.api[21]! cert address
    if matched != 1 then throw (K.eacces ())
  finally Prim.void1 c.api[23]! cert

private partial def tlsHandshake (deadline : Nat) : NetM Unit := do
  if (← remaining deadline) == 0 then throw (K.etimedout ())
  let c ← transport.get
  let some fd := c.fd | throw (K.enotconn ())
  let (count, want, _) ← tlsStep c do
    let (error, rc) ← Prim.tlsConnect c.api[16]! c.ssl
    pure (error, rc, ByteArray.empty)
  if count != 0 then return
  if want != 0 then
    discard <| waitFd fd want true deadline
  tlsHandshake deadline

private def tlsCall (action : UInt32 → BaseIO (Prim.Result α)) : NetM α := do
  let (error, value) ← action (← transport.get).nativeErrno
  transport.modify fun c => { c with nativeErrno := error }
  return value

private def tlsInitError : NetM α := do
  throw (← transport.get).nativeErrno

private def tlsStart (host : String) (verify : Bool) (ca cert key : String) (deadline : Nat) :
    NetM Unit := do
  tlsLoad
  transport.modify fun c => { c with nativeErrno := K.eproto () }
  let c ← transport.get
  let method ← tlsCall (Prim.ptr0 c.api[0]!)
  let ctx ← tlsCall (Prim.ptr1 c.api[1]! method)
  if ctx == 0 then tlsInitError
  transport.modify fun c => { c with ctx }
  if (← tlsCall (Prim.ctrl c.api[3]! ctx K.minProtoVersion K.tls12.toUInt64)) != 1 then
    tlsInitError
  tlsCall (Prim.verify c.api[4]! ctx (if verify then K.verifyPeer else K.verifyNone))
  if verify then
    let rc ← tlsCall (if ca.isEmpty then Prim.int1 c.api[6]! ctx else Prim.ca c.api[5]! ctx ca)
    if rc != 1 then tlsInitError
  if !cert.isEmpty then
    if (← tlsCall (Prim.cert c.api[7]! ctx cert)) != 1 then tlsInitError
    if (← tlsCall (Prim.key c.api[8]! ctx (if key.isEmpty then cert else key))) != 1 then
      tlsInitError
    if (← tlsCall (Prim.int1 c.api[9]! ctx)) != 1 then tlsInitError
  let ssl ← tlsCall (Prim.ptr1 c.api[10]! ctx)
  transport.modify fun c => { c with ssl }
  if ssl == 0 then tlsInitError
  let some fd := c.fd | throw (K.enotconn ())
  if (← tlsCall (Prim.int2 c.api[12]! ssl fd)) != 1 then tlsInitError
  let ipv4 ← Prim.numeric (K.inet ()) host
  let numeric ← if ipv4 == 1 then pure true else do
    pure ((← Prim.numeric (K.inet6 ()) host) == 1)
  if !numeric && (← tlsCall (Prim.sni c.api[13]! ssl host)) != 1 then tlsInitError
  let pipeMask ← checked (← Prim.sigemptyset)
  let pipeMask ← checked (← Prim.sigaddset pipeMask (K.sigpipe ()))
  transport.modify fun c => { c with pipeMask }
  tlsHandshake deadline
  if verify then
    if (← Prim.long1 c.api[15]! ssl) != 0 then throw (K.eacces ())
    tlsIdentity host

private def connect (host service : String) (tls : Bool) (timeout : UInt32)
    (keepalive verify : Bool) (ca cert key : String) : IO Unit := do
  reset
  transport.modify fun c => { c with timeout }
  let deadline ← runNet "clock" (deadlineNew timeout)
  let addresses ← resolve host service deadline
  runNet "connect" (connectAddresses addresses keepalive deadline)
  if tls then
    match ← (tlsStart host verify ca cert key deadline).toBaseIO with
    | .ok _ => pure ()
    | .error error =>
      let c ← transport.get
      let reason ← if c.api.size > 26 then
          Prim.reason c.api[26]! (← Prim.ulong0 c.api[25]!)
        else pure none
      let reason ← match reason with
        | some reason => pure reason
        | none =>
          if error == K.eacces () then pure "certificate verify failed"
          else Prim.errorText error
      let detail ← Prim.errorText c.tlsErrno
      let stage := if c.ssl != 0 then "handshake" else "initialization"
      reset
      throw (IO.userError (s!"TLS connection to {host}:{service} failed: {reason}\n" ++
        s!"TLS {stage} was unsuccessful: {detail}"))

private def relay (mask : UInt32) : IO Unit := do
  if mask &&& 4294967264 != 0 then transportFailure "relay" (K.einval ())
  let c ← transport.get
  if mask != 0 && c.fd.isNone then transportFailure "relay" (K.enotconn ())
  transport.set { c with streams := mask }

def active : IO Bool := do return (← transport.get).streams != 0

def streamEnabled (stream : UInt32) : IO Bool := do
  return stream < 5 && (← transport.get).streams &&& (1 <<< stream) != 0

private def enqueue (bytes : ByteArray) : IO Unit := pendingMessages.modify (·.push bytes)

private def queueClose : IO Unit := pendingMessages.set #[]

def endpoint (value : String) : Option (String × String × Bool) := do
  let tls := value.endsWith "(tls)"
  let value := if tls then value.dropEnd 5 |>.toString else value
  let defaultPort := if tls then "30344" else "30343"
  let (host, port) ← if value.startsWith "[" then do
      let parts := value.splitOn "]"
      match parts with
      | [host, rest] =>
        let host := host.drop 1 |>.toString
        if rest.isEmpty then some (host, defaultPort)
        else if rest.startsWith ":" then some (host, rest.drop 1 |>.toString) else none
      | _ => none
    else match value.splitOn ":" with
      | [host] => some (host, defaultPort)
      | [host, port] => some (host, port)
      | _ => none
  let number ← port.toNat?
  if host.isEmpty || number == 0 || number > 65535 then none else some (host, port, tls)

private structure Session where
  settings : Settings
  io : Bool
  ignoreErrors : Bool
  subcommands : Bool := false
  logId : String := ""
  started : Nat
  last : Nat
  elapsed : Nat := 0
  committed : Nat := 0
  commitSeen : Bool := false

initialize current : IO.Ref (Option Session) ← IO.mkRef none

private def timespec (nanos : Nat) : TimeSpec :=
  { seconds := Int.ofNat (nanos / 1000000000), nanoseconds := Int.ofNat (nanos % 1000000000) }

private def sendMessage (message : ClientMessage) : IO Unit := send (encodeClient message)

private def readMessage (wait : Bool) : IO (Option ServerMessage) := do
  let some bytes ← receive wait | return none
  let some message := decodeServer bytes |
    throw (IO.userError s!"unable to unpack ServerMessage size {bytes.size}")
  return some message

private def connectServer (st : Settings) (server : String) : IO Unit := do
  let some (host, port, tls) := endpoint server |
    throw (IO.userError ("invalid log server: " ++ server))
  connect host port tls st.logServerTimeout.toUInt32 st.logServerKeepalive st.logServerVerify
    (st.logServerCabundle.getD "") (st.logServerPeerCert.getD "") (st.logServerPeerKey.getD "")

private def handshake : IO Bool := do
  sendMessage (.hello "sudoers 1.9.17p2")
  match ← readMessage true with
  | some (.hello hello) =>
    if hello.serverId.isEmpty then throw (IO.userError "invalid ServerHello")
    return hello.subcommands
  | some (.error error) => throw (IO.userError ("error message received from server: " ++ error))
  | some (.abort error) => throw (IO.userError ("abort message received from server: " ++ error))
  | _ => throw (IO.userError "invalid ServerHello")

private def connectFirst (st : Settings) (servers : List String) : IO Bool := do
  let mut cause : Option String := none
  for server in servers do
    let connected ← try
      connectServer st server
      pure true
    catch error =>
      let message := error.toString
      if message.startsWith "TLS connection to " then
        let lines := message.splitOn "\n"
        Sys.writeStderr ("sudo: " ++ lines.headD message ++ "\n")
        cause := (lines.drop 1).head?
      closeTransport
      pure false
    if connected then return ← handshake
  for message in cause do Sys.writeStderr ("sudo: " ++ message ++ "\n")
  throw (IO.userError "unable to connect to log server")

private def consume (s : Session) (message : ServerMessage) : IO Session := do
  match message with
  | .commit time =>
    if !s.io || time.seconds < 0 || time.nanoseconds < 0 || time.nanoseconds >= 1000000000 then
      throw (IO.userError "invalid log server commit point")
    let committed := time.seconds.toNat * 1000000000 + time.nanoseconds.toNat
    if committed < s.committed || committed > s.elapsed then
      throw (IO.userError "invalid log server commit point")
    return { s with committed, commitSeen := true }
  | .logId id =>
    if id.isEmpty then throw (IO.userError "invalid log server log ID")
    return { s with logId := id }
  | .error message => throw (IO.userError ("error message received from server: " ++ message))
  | .abort message => throw (IO.userError ("abort message received from server: " ++ message))
  | .hello _ => throw (IO.userError "unexpected ServerHello")

private partial def awaitId (s : Session) : IO Session := do
  if !s.logId.isEmpty then return s
  let some message ← readMessage true | throw (IO.userError "log server closed connection")
  awaitId (← consume s message)

private partial def awaitCommit (s : Session) : IO Session := do
  if s.commitSeen && s.committed == s.elapsed then return s
  let some message ← readMessage true | throw (IO.userError "log server closed connection")
  awaitCommit (← consume s message)

private partial def drain (s : Session) : IO Session := do
  let some message ← readMessage false | return s
  drain (← consume s message)

private def failure (s : Session) (error : IO.Error) : IO Unit := do
  closeTransport
  current.set none
  Sys.writeStderr ("sudo: " ++ error.toString ++ "\n")
  if !s.ignoreErrors then
    throw (IO.userError "unexpected child termination condition: 0")

private def info (d : EventLog.Details) : List InfoMessage :=
  d.fields.filterMap fun (key, value) => match value with
    | .string s => some { key, value := .string s }
    | .number n => some { key, value := .number n }
    | .array xs => some { key, value := .strings (xs.filterMap fun x => match x with
        | .string s => some s | _ => none) }
    | _ => none

def close : IO Unit := do
  current.set none
  closeTransport
  queueClose

private def streamMask (plan : Option LeanSudo.IoLog.Plan) : UInt32 :=
  match plan with
  | none => 0
  | some p =>
    let bits := [p.stdin, p.stdout, p.stderr, p.ttyin, p.ttyout]
    (bits.zipIdx.foldl (fun (n : Nat) (b, i) => if b then n + 2 ^ i else n) 0).toUInt32
def accept (st : Settings) (details : EventLog.Details) (plan : Option LeanSudo.IoLog.Plan)
    (configureFilter : UInt32 → Array String → IO Unit) : IO Unit := do
  if st.logServers.isEmpty || (!st.logAllowed && plan.isNone) then return
  let io := plan.isSome
  let ignoreErrors := if io then st.ignoreIologErrors else st.ignoreLogfileErrors
  try
    let started ← awakeTime
    let subcommands ← connectFirst st st.logServers
    let now ← Sys.eventTime false st.sudoersLocale
    sendMessage (.accept { seconds := now.seconds, nanoseconds := now.nanoseconds } (info details) io)
    let s : Session := {
      settings := st, io, ignoreErrors, subcommands
      started, last := started }
    let s ← if io then awaitId s else pure s
    if let some p := plan then
      configureFilter ((if p.ignoreErrors then 128 else 0) + (if p.logPasswords then 256 else 0)) p.passpromptRegex
      relay (streamMask plan)
    queueClose
    current.set (some s)
  catch error =>
    close
    Sys.writeStderr ("sudo: " ++ error.toString ++ "\n")
    if !ignoreErrors then
      throw (IO.userError (if io then "error initializing I/O plugin sudoers_io"
        else "sudoers_audit: unable to log accept event"))

def event (st : Settings) (details : EventLog.Details) (reason : String) (alert : Bool := false) : IO Unit := do
  if st.logServers.isEmpty || (!alert && !st.logDenied) then return
  if ← broker.get then
    let some s ← current.get | return
    if !s.subcommands then return
    let now ← Sys.eventTime false st.sudoersLocale
    let time : TimeSpec := { seconds := now.seconds, nanoseconds := now.nanoseconds }
    enqueue (encodeClient (if alert then .alert time "" (info details) else .reject time "" (info details)))
    return
  try
    let _ ← connectFirst st st.logServers
    let now ← Sys.eventTime false st.sudoersLocale
    let time : TimeSpec := { seconds := now.seconds, nanoseconds := now.nanoseconds }
    sendMessage (if alert then .alert time reason (info details) else .reject time reason (info details))
  catch error => Sys.writeStderr ("sudo: " ++ error.toString ++ "\n")
  finally closeTransport

def poll : IO Unit := do
  let some s ← current.get | return
  try
    let messages ← pendingMessages.modifyGet fun messages => (messages, #[])
    let mut s := s
    for bytes in messages do
      send bytes
      s ← drain s
    if (← active) then s ← drain s
    current.set (some s)
  catch error => failure s error

def subcommand (details : EventLog.Details) (reason : Option String) : IO Unit := do
  let some s ← current.get | return
  if !s.subcommands then return
  let now ← Sys.eventTime false s.settings.sudoersLocale
  let time : TimeSpec := { seconds := now.seconds, nanoseconds := now.nanoseconds }
  let message := match reason with
    | some _ => ClientMessage.reject time "" (info details)
    | none => .accept time (info details) s.io
  enqueue (encodeClient message)


def ioEvent (event : UInt32) (data : ByteArray) (a b : UInt32) : IO Unit := do
  if !(← active) then return
  if event < 5 && !(← streamEnabled event) then return
  let some s ← current.get | return
  try
    let now ← awakeTime
    let delay := now - s.last
    let time := timespec delay
    let message := if event.toNat < 5 then ClientMessage.io event.toNat time data
      else if event == 5 then .winsize time a.toNat b.toNat
      else .suspend time (String.fromUTF8! data)
    let bytes := encodeClient message
    let s := { s with last := now, elapsed := s.elapsed + delay }
    send bytes
    let s ← drain s
    current.set (some s)
  catch error => failure s error

def finish (exitValue : Nat) (signal : String) (dumpedCore : Bool)
    (error : String := "") : IO Unit := do
  poll
  let some s ← current.get | return
  if !s.io then
    close
    return
  let s := { s with commitSeen := false }
  try
    let runtime := (← awakeTime) - s.started
    let bytes := encodeClient (.exit (timespec runtime) (Int.ofNat exitValue) dumpedCore signal error)
    send bytes
    let _ ← awaitCommit s
    pure ()
  catch error => failure s error
  finally close

end LeanSudo.Sys.LogSrv
