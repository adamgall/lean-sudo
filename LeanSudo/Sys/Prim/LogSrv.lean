namespace LeanSudo.Sys.Prim.LogSrv

abbrev Result (α : Type) := UInt32 × α

namespace Constants
@[extern "ls_logprim_eintr"] opaque eintr : Unit → UInt32
@[extern "ls_logprim_eio"] opaque eio : Unit → UInt32
@[extern "ls_logprim_etimedout"] opaque etimedout : Unit → UInt32
@[extern "ls_logprim_ebadf"] opaque ebadf : Unit → UInt32
@[extern "ls_logprim_enodata"] opaque enodata : Unit → UInt32
@[extern "ls_logprim_eproto"] opaque eproto : Unit → UInt32
@[extern "ls_logprim_enotconn"] opaque enotconn : Unit → UInt32
@[extern "ls_logprim_eagain"] opaque eagain : Unit → UInt32
@[extern "ls_logprim_ewouldblock"] opaque ewouldblock : Unit → UInt32
@[extern "ls_logprim_emsgsize"] opaque emsgsize : Unit → UInt32
@[extern "ls_logprim_epipe"] opaque epipe : Unit → UInt32
@[extern "ls_logprim_ehostunreach"] opaque ehostunreach : Unit → UInt32
@[extern "ls_logprim_einprogress"] opaque einprogress : Unit → UInt32
@[extern "ls_logprim_ealready"] opaque ealready : Unit → UInt32
@[extern "ls_logprim_enosys"] opaque enosys : Unit → UInt32
@[extern "ls_logprim_eacces"] opaque eacces : Unit → UInt32
@[extern "ls_logprim_eafnosupport"] opaque eafnosupport : Unit → UInt32
@[extern "ls_logprim_einval"] opaque einval : Unit → UInt32
@[extern "ls_logprim_getfd"] opaque getfd : Unit → UInt32
@[extern "ls_logprim_setfd"] opaque setfd : Unit → UInt32
@[extern "ls_logprim_cloexec"] opaque cloexec : Unit → UInt32
@[extern "ls_logprim_getfl"] opaque getfl : Unit → UInt32
@[extern "ls_logprim_setfl"] opaque setfl : Unit → UInt32
@[extern "ls_logprim_nonblock"] opaque nonblock : Unit → UInt32
@[extern "ls_logprim_pollin"] opaque pollin : Unit → UInt32
@[extern "ls_logprim_pollout"] opaque pollout : Unit → UInt32
@[extern "ls_logprim_pollnval"] opaque pollnval : Unit → UInt32
@[extern "ls_logprim_pollerr"] opaque pollerr : Unit → UInt32
@[extern "ls_logprim_pollhup"] opaque pollhup : Unit → UInt32
@[extern "ls_logprim_inet"] opaque inet : Unit → UInt32
@[extern "ls_logprim_inet6"] opaque inet6 : Unit → UInt32
@[extern "ls_logprim_unspec"] opaque unspec : Unit → UInt32
@[extern "ls_logprim_stream"] opaque stream : Unit → UInt32
@[extern "ls_logprim_tcp"] opaque tcp : Unit → UInt32
@[extern "ls_logprim_sigpipe"] opaque sigpipe : Unit → UInt32
@[extern "ls_logprim_sockaddrStorageSize"] opaque sockaddrStorageSize : Unit → UInt32
@[extern "ls_logprim_sigkill"] opaque sigkill : Unit → UInt32
@[extern "ls_logprim_intMax"] opaque intMax : Unit → UInt32
@[extern "ls_logprim_ipv4Offset"] opaque ipv4Offset : Unit → UInt32
@[extern "ls_logprim_ipv4Size"] opaque ipv4Size : Unit → UInt32
@[extern "ls_logprim_sockaddr4Size"] opaque sockaddr4Size : Unit → UInt32
@[extern "ls_logprim_ipv6Offset"] opaque ipv6Offset : Unit → UInt32
@[extern "ls_logprim_ipv6Size"] opaque ipv6Size : Unit → UInt32
@[extern "ls_logprim_sockaddr6Size"] opaque sockaddr6Size : Unit → UInt32
def sslWantRead : UInt32 := 2
def sslWantWrite : UInt32 := 3
def sslSyscall : UInt32 := 5
def sslZeroReturn : UInt32 := 6
def noPartialWildcards : UInt32 := 4
def neverCheckSubject : UInt32 := 0x20
def minProtoVersion : UInt32 := 123
def tls12 : UInt32 := 0x0303
def verifyPeer : UInt32 := 1
def verifyNone : UInt32 := 0
end Constants

@[extern "ls_logprim_clock"] opaque clock : BaseIO (Result (UInt64 × UInt64))
@[extern "ls_logprim_error"] opaque errorText (error : UInt32) : BaseIO String
@[extern "ls_logprim_gai_error"] opaque gaiErrorText (error : UInt32) : BaseIO String
@[extern "ls_logprim_resolve"] opaque resolve (host service : @& String)
    (family kind protocol : UInt32) : BaseIO (Result UInt64)
@[extern "ls_logprim_address"] opaque address (node : UInt64) :
    BaseIO (UInt64 × UInt32 × UInt32 × UInt32 × UInt32 × ByteArray)
@[extern "ls_logprim_free_addresses"] opaque freeAddresses (node : UInt64) : BaseIO Unit
@[extern "ls_logprim_socketpair"] opaque socketpair : BaseIO (Result (UInt32 × UInt32))
@[extern "ls_logprim_socket"] opaque socket (family kind protocol : UInt32) : BaseIO (Result UInt32)
@[extern "ls_logprim_fcntl"] opaque fcntl (fd command value : UInt32) : BaseIO (Result UInt32)
@[extern "ls_logprim_keepalive"] opaque keepalive (fd : UInt32) (enabled : Bool) :
    BaseIO (Result UInt32)
@[extern "ls_logprim_connect"] opaque connect (fd : UInt32) (address : @& ByteArray) :
    BaseIO (Result UInt32)
@[extern "ls_logprim_socket_error"] opaque socketError (fd : UInt32) : BaseIO (Result UInt32)
@[extern "ls_logprim_close"] opaque close (fd : UInt32) : BaseIO (Result UInt32)
@[extern "ls_logprim_poll"] opaque poll (fd events timeout : UInt32) : BaseIO (Result UInt32)
@[extern "ls_logprim_send"] opaque send (fd : UInt32) (bytes : @& ByteArray)
    (offset count : USize) : BaseIO (Result UInt64)
@[extern "ls_logprim_recv"] opaque recv (fd : UInt32) (bytes : ByteArray)
    (offset count : USize) : BaseIO (UInt32 × UInt64 × ByteArray)
@[extern "ls_logprim_peer"] opaque peer (fd : UInt32) : BaseIO (Result (UInt32 × ByteArray))
@[extern "ls_logprim_numeric"] opaque numeric (family : UInt32) (host : @& String) : BaseIO UInt32
@[extern "ls_logprim_sigemptyset"] opaque sigemptyset : BaseIO (Result ByteArray)
@[extern "ls_logprim_sigaddset"] opaque sigaddset (mask : ByteArray) (signal : UInt32) :
    BaseIO (Result ByteArray)
@[extern "ls_logprim_sigpending"] opaque sigpending : BaseIO (Result ByteArray)
@[extern "ls_logprim_sigismember"] opaque sigismember (mask : @& ByteArray) (signal : UInt32) :
    BaseIO (Result UInt32)
@[extern "ls_logprim_sigtimedwait"] opaque sigtimedwait (mask : @& ByteArray) (timeout : UInt32) :
    BaseIO (Result UInt32)
@[extern "ls_logprim_open_library"] opaque openLibrary (name : @& String) : BaseIO UInt64
@[extern "ls_logprim_symbol"] opaque symbol (library : UInt64) (name : @& String) : BaseIO UInt64
@[extern "ls_logprim_close_library"] opaque closeLibrary (library : UInt64) : BaseIO UInt32
@[extern "ls_logprim_ptr0"] opaque ptr0 (fn : UInt64) (prior : UInt32) : BaseIO (Result UInt64)
@[extern "ls_logprim_ptr1"] opaque ptr1 (fn arg : UInt64) (prior : UInt32) : BaseIO (Result UInt64)
@[extern "ls_logprim_ulong0"] opaque ulong0 (fn : UInt64) : BaseIO UInt64
@[extern "ls_logprim_void0"] opaque void0 (fn : UInt64) : BaseIO Unit
@[extern "ls_logprim_void1"] opaque void1 (fn arg : UInt64) : BaseIO Unit
@[extern "ls_logprim_int1"] opaque int1 (fn arg : UInt64) (prior : UInt32) : BaseIO (Result UInt32)
@[extern "ls_logprim_long1"] opaque long1 (fn arg : UInt64) : BaseIO UInt64
@[extern "ls_logprim_int2"] opaque int2 (fn arg : UInt64) (value prior : UInt32) :
    BaseIO (Result UInt32)
@[extern "ls_logprim_ctrl"] opaque ctrl (fn arg : UInt64) (command : UInt32)
    (value : UInt64) (prior : UInt32) : BaseIO (Result UInt64)
@[extern "ls_logprim_verify"] opaque verify (fn ctx : UInt64) (mode prior : UInt32) :
    BaseIO (Result Unit)
@[extern "ls_logprim_ca"] opaque ca (fn ctx : UInt64) (path : @& String)
    (prior : UInt32) : BaseIO (Result UInt32)
@[extern "ls_logprim_cert"] opaque cert (fn ctx : UInt64) (path : @& String)
    (prior : UInt32) : BaseIO (Result UInt32)
@[extern "ls_logprim_key"] opaque key (fn ctx : UInt64) (path : @& String)
    (prior : UInt32) : BaseIO (Result UInt32)
@[extern "ls_logprim_sni"] opaque sni (fn ssl : UInt64) (host : @& String)
    (prior : UInt32) : BaseIO (Result UInt64)
@[extern "ls_logprim_tls_connect"] opaque tlsConnect (fn ssl : UInt64) : BaseIO (Result UInt32)
@[extern "ls_logprim_tls_send"] opaque tlsSend (fn ssl : UInt64) (bytes : @& ByteArray)
    (offset count : USize) : BaseIO (Result UInt32)
@[extern "ls_logprim_tls_recv"] opaque tlsRecv (fn ssl : UInt64) (bytes : ByteArray)
    (offset count : USize) : BaseIO (UInt32 × UInt32 × ByteArray)
@[extern "ls_logprim_cert_host"] opaque certHost (fn cert : UInt64) (host : @& String)
    (length : USize) (flags : UInt32) : BaseIO UInt32
@[extern "ls_logprim_cert_ip"] opaque certIp (fn cert : UInt64) (address : @& ByteArray) :
    BaseIO UInt32
@[extern "ls_logprim_cert_ext"] opaque certExt (fn cert : UInt64) : BaseIO UInt32
@[extern "ls_logprim_reason"] opaque reason (fn error : UInt64) : BaseIO (Option String)
end LeanSudo.Sys.Prim.LogSrv
