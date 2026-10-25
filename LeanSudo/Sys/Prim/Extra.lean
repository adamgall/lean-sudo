import Std

namespace LeanSudo.Sys.Prim.Extra

@[extern "leansudo_extra_signal_description"]
opaque signalDescription (signal : UInt32) : IO String

structure Constants where
  regExtended : UInt32
  regNosub : UInt32
  regIcase : UInt32
  regNomatch : UInt32
  regBadbr : UInt32
  regBadrpt : UInt32
  globNomatch : UInt32
  iffUp : UInt32
  iffLoopback : UInt32
  afInet : UInt32
  afInet6 : UInt32
  afNetlink : UInt32
  sockRaw : UInt32
  sockCloexec : UInt32
  netlinkAudit : UInt32
  enomem : UInt32
  eafnosupport : UInt32
  eprotonosupport : UInt32
  einval : UInt32
  econnrefused : UInt32
  auditUserCmd : UInt32
  nlmRequest : UInt32
  nlmAck : UInt32
  nlmsgError : UInt32
  nlHeaderSize : UInt32
  nlLengthOffset : UInt32
  nlTypeOffset : UInt32
  nlFlagsOffset : UInt32
  nlSequenceOffset : UInt32
  nlPidOffset : UInt32
  nlLengthWidth : UInt32
  nlTypeWidth : UInt32
  nlFlagsWidth : UInt32
  nlSequenceWidth : UInt32
  nlPidWidth : UInt32
  nlErrorSize : UInt32
  nlErrorOffset : UInt32
  nlErrorWidth : UInt32
  intMax : UInt32
  deriving Inhabited

@[extern "leansudo_extra_constants"]
opaque constants (_ : Unit) : Constants

@[extern "leansudo_extra_domain"]
opaque domain : IO (UInt32 × String)
@[extern "leansudo_extra_locale_new"]
opaque localeNew (name : @& String) : IO (UInt32 × USize)
@[extern "leansudo_extra_locale_use"]
opaque localeUse (locale : USize) : IO (UInt32 × USize)
@[extern "leansudo_extra_locale_free"]
opaque localeFree (locale : USize) : IO Unit
@[extern "leansudo_extra_regex_alloc"]
opaque regexAlloc : IO USize
@[extern "leansudo_extra_free"]
opaque free (value : USize) : IO Unit
@[extern "leansudo_extra_regex_compile"]
opaque regexCompile (value : USize) (pattern : @& String) (flags : UInt32) : IO UInt32
@[extern "leansudo_extra_regex_error"]
opaque regexError (status : UInt32) (value : USize) : IO String
@[extern "leansudo_extra_regex_exec"]
opaque regexExec (value : USize) (text : @& String) : IO UInt32
@[extern "leansudo_extra_regex_free"]
opaque regexFree (value : USize) : IO Unit
@[extern "leansudo_extra_glob_alloc"]
opaque globAlloc : IO USize
@[extern "leansudo_extra_glob"]
opaque glob (value : USize) (pattern : @& String) : IO UInt32
@[extern "leansudo_extra_glob_count"]
opaque globCount (value : USize) : IO USize
@[extern "leansudo_extra_glob_path"]
opaque globPath (value index : USize) : IO String
@[extern "leansudo_extra_glob_free"]
opaque globFree (value : USize) : IO Unit
@[extern "leansudo_extra_interfaces"]
opaque interfaces : IO (UInt32 × USize)
@[extern "leansudo_extra_interfaces_free"]
opaque interfacesFree (value : USize) : IO Unit
@[extern "leansudo_extra_interface_next"]
opaque interfaceNext (value : USize) : IO USize
@[extern "leansudo_extra_interface_address"]
opaque interfaceAddress (value : USize) : IO USize
@[extern "leansudo_extra_interface_mask"]
opaque interfaceMask (value : USize) : IO USize
@[extern "leansudo_extra_interface_flags"]
opaque interfaceFlags (value : USize) : IO UInt32
@[extern "leansudo_extra_address_family"]
opaque addressFamily (value : USize) : IO UInt32
@[extern "leansudo_extra_address_v4"]
opaque addressV4 (value : USize) : IO USize
@[extern "leansudo_extra_address_v6"]
opaque addressV6 (value : USize) : IO USize
@[extern "leansudo_extra_address_text"]
opaque addressText (family : UInt32) (value : USize) : IO (Option String)
@[extern "leansudo_extra_hostname"]
opaque hostname (host : @& String) : IO (UInt32 × USize)
@[extern "leansudo_extra_hostname_name"]
opaque hostnameName (value : USize) : IO (Option String)
@[extern "leansudo_extra_hostname_error"]
opaque hostnameError (status : UInt32) : IO String
@[extern "leansudo_extra_hostname_free"]
opaque hostnameFree (value : USize) : IO Unit
@[extern "leansudo_extra_socket"]
opaque socket (family type protocol : UInt32) : IO (UInt32 × UInt32)
@[extern "leansudo_extra_close"]
opaque close (fd : UInt32) : IO UInt32
@[extern "leansudo_extra_cwd"]
opaque cwd : IO (Option ByteArray)
@[extern "leansudo_extra_readlink"]
opaque readlink (path : @& String) : IO (Option ByteArray)
@[extern "leansudo_extra_netlink_send"]
opaque netlinkSend (fd : UInt32) (bytes : @& ByteArray) : IO UInt32
@[extern "leansudo_extra_poll"]
opaque poll (fd : UInt32) (timeout : Int32) : IO (Int32 × UInt32)
@[extern "leansudo_extra_netlink_receive"]
opaque netlinkReceive (fd : UInt32) : IO (Option (UInt32 × ByteArray))
@[extern "leansudo_extra_little_endian"]
opaque littleEndian (_ : Unit) : Bool

def withLocale (name error : String) (action : IO α) : IO α := do
  let name :=
    if name.contains '\x00' then String.ofList (name.toList.takeWhile (· != '\x00'))
    else name
  let (baseStatus, base) ← localeNew "C"
  if baseStatus != 0 then throw (IO.userError error)
  try
    let (status, selected) ←
      if name.isEmpty || name == "C" || name == "POSIX" then pure (0, base)
      else localeNew name
    if status == (constants ()).enomem then throw (IO.userError error)
    let selected := if status == 0 then selected else base
    try
      let (useStatus, previous) ← localeUse selected
      if useStatus != 0 then throw (IO.userError error)
      try action
      finally
        let _ ← localeUse previous
        pure ()
    finally
      if selected != base then localeFree selected
  finally
    localeFree base

end LeanSudo.Sys.Prim.Extra
