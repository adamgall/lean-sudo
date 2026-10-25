import Std

namespace LeanSudo.Sys.Prim.CoreLogs

structure TimeFields where
  fields : Array Int32
  zone : ByteArray
  offset : Int64
  deriving Inhabited

@[extern "lean_corelogs_ABDAY_1"] opaque ABDAY_1 : Unit → UInt32
@[extern "lean_corelogs_ABDAY_2"] opaque ABDAY_2 : Unit → UInt32
@[extern "lean_corelogs_ABDAY_3"] opaque ABDAY_3 : Unit → UInt32
@[extern "lean_corelogs_ABDAY_4"] opaque ABDAY_4 : Unit → UInt32
@[extern "lean_corelogs_ABDAY_5"] opaque ABDAY_5 : Unit → UInt32
@[extern "lean_corelogs_ABDAY_6"] opaque ABDAY_6 : Unit → UInt32
@[extern "lean_corelogs_ABDAY_7"] opaque ABDAY_7 : Unit → UInt32
@[extern "lean_corelogs_DAY_1"] opaque DAY_1 : Unit → UInt32
@[extern "lean_corelogs_DAY_2"] opaque DAY_2 : Unit → UInt32
@[extern "lean_corelogs_DAY_3"] opaque DAY_3 : Unit → UInt32
@[extern "lean_corelogs_DAY_4"] opaque DAY_4 : Unit → UInt32
@[extern "lean_corelogs_DAY_5"] opaque DAY_5 : Unit → UInt32
@[extern "lean_corelogs_DAY_6"] opaque DAY_6 : Unit → UInt32
@[extern "lean_corelogs_DAY_7"] opaque DAY_7 : Unit → UInt32
@[extern "lean_corelogs_ABMON_1"] opaque ABMON_1 : Unit → UInt32
@[extern "lean_corelogs_ABMON_2"] opaque ABMON_2 : Unit → UInt32
@[extern "lean_corelogs_ABMON_3"] opaque ABMON_3 : Unit → UInt32
@[extern "lean_corelogs_ABMON_4"] opaque ABMON_4 : Unit → UInt32
@[extern "lean_corelogs_ABMON_5"] opaque ABMON_5 : Unit → UInt32
@[extern "lean_corelogs_ABMON_6"] opaque ABMON_6 : Unit → UInt32
@[extern "lean_corelogs_ABMON_7"] opaque ABMON_7 : Unit → UInt32
@[extern "lean_corelogs_ABMON_8"] opaque ABMON_8 : Unit → UInt32
@[extern "lean_corelogs_ABMON_9"] opaque ABMON_9 : Unit → UInt32
@[extern "lean_corelogs_ABMON_10"] opaque ABMON_10 : Unit → UInt32
@[extern "lean_corelogs_ABMON_11"] opaque ABMON_11 : Unit → UInt32
@[extern "lean_corelogs_ABMON_12"] opaque ABMON_12 : Unit → UInt32
@[extern "lean_corelogs_MON_1"] opaque MON_1 : Unit → UInt32
@[extern "lean_corelogs_MON_2"] opaque MON_2 : Unit → UInt32
@[extern "lean_corelogs_MON_3"] opaque MON_3 : Unit → UInt32
@[extern "lean_corelogs_MON_4"] opaque MON_4 : Unit → UInt32
@[extern "lean_corelogs_MON_5"] opaque MON_5 : Unit → UInt32
@[extern "lean_corelogs_MON_6"] opaque MON_6 : Unit → UInt32
@[extern "lean_corelogs_MON_7"] opaque MON_7 : Unit → UInt32
@[extern "lean_corelogs_MON_8"] opaque MON_8 : Unit → UInt32
@[extern "lean_corelogs_MON_9"] opaque MON_9 : Unit → UInt32
@[extern "lean_corelogs_MON_10"] opaque MON_10 : Unit → UInt32
@[extern "lean_corelogs_MON_11"] opaque MON_11 : Unit → UInt32
@[extern "lean_corelogs_MON_12"] opaque MON_12 : Unit → UInt32
@[extern "lean_corelogs_ALTMON_1"] opaque ALTMON_1 : Unit → UInt32
@[extern "lean_corelogs_ALTMON_2"] opaque ALTMON_2 : Unit → UInt32
@[extern "lean_corelogs_ALTMON_3"] opaque ALTMON_3 : Unit → UInt32
@[extern "lean_corelogs_ALTMON_4"] opaque ALTMON_4 : Unit → UInt32
@[extern "lean_corelogs_ALTMON_5"] opaque ALTMON_5 : Unit → UInt32
@[extern "lean_corelogs_ALTMON_6"] opaque ALTMON_6 : Unit → UInt32
@[extern "lean_corelogs_ALTMON_7"] opaque ALTMON_7 : Unit → UInt32
@[extern "lean_corelogs_ALTMON_8"] opaque ALTMON_8 : Unit → UInt32
@[extern "lean_corelogs_ALTMON_9"] opaque ALTMON_9 : Unit → UInt32
@[extern "lean_corelogs_ALTMON_10"] opaque ALTMON_10 : Unit → UInt32
@[extern "lean_corelogs_ALTMON_11"] opaque ALTMON_11 : Unit → UInt32
@[extern "lean_corelogs_ALTMON_12"] opaque ALTMON_12 : Unit → UInt32
@[extern "lean_corelogs_ABALTMON_1"] opaque ABALTMON_1 : Unit → UInt32
@[extern "lean_corelogs_ABALTMON_2"] opaque ABALTMON_2 : Unit → UInt32
@[extern "lean_corelogs_ABALTMON_3"] opaque ABALTMON_3 : Unit → UInt32
@[extern "lean_corelogs_ABALTMON_4"] opaque ABALTMON_4 : Unit → UInt32
@[extern "lean_corelogs_ABALTMON_5"] opaque ABALTMON_5 : Unit → UInt32
@[extern "lean_corelogs_ABALTMON_6"] opaque ABALTMON_6 : Unit → UInt32
@[extern "lean_corelogs_ABALTMON_7"] opaque ABALTMON_7 : Unit → UInt32
@[extern "lean_corelogs_ABALTMON_8"] opaque ABALTMON_8 : Unit → UInt32
@[extern "lean_corelogs_ABALTMON_9"] opaque ABALTMON_9 : Unit → UInt32
@[extern "lean_corelogs_ABALTMON_10"] opaque ABALTMON_10 : Unit → UInt32
@[extern "lean_corelogs_ABALTMON_11"] opaque ABALTMON_11 : Unit → UInt32
@[extern "lean_corelogs_ABALTMON_12"] opaque ABALTMON_12 : Unit → UInt32
@[extern "lean_corelogs_AM_STR"] opaque AM_STR : Unit → UInt32
@[extern "lean_corelogs_PM_STR"] opaque PM_STR : Unit → UInt32
@[extern "lean_corelogs_D_T_FMT"] opaque D_T_FMT : Unit → UInt32
@[extern "lean_corelogs_D_FMT"] opaque D_FMT : Unit → UInt32
@[extern "lean_corelogs_T_FMT"] opaque T_FMT : Unit → UInt32
@[extern "lean_corelogs_T_FMT_AMPM"] opaque T_FMT_AMPM : Unit → UInt32
@[extern "lean_corelogs_ERA"] opaque ERA : Unit → UInt32
@[extern "lean_corelogs_ERA_D_T_FMT"] opaque ERA_D_T_FMT : Unit → UInt32
@[extern "lean_corelogs_ERA_D_FMT"] opaque ERA_D_FMT : Unit → UInt32
@[extern "lean_corelogs_ERA_T_FMT"] opaque ERA_T_FMT : Unit → UInt32
@[extern "lean_corelogs_ALT_DIGITS"] opaque ALT_DIGITS : Unit → UInt32

@[extern "lean_corelogs_LOG_AUTHPRIV"] opaque LOG_AUTHPRIV : Unit → UInt32
@[extern "lean_corelogs_LOG_AUTH"] opaque LOG_AUTH : Unit → UInt32
@[extern "lean_corelogs_LOG_DAEMON"] opaque LOG_DAEMON : Unit → UInt32
@[extern "lean_corelogs_LOG_USER"] opaque LOG_USER : Unit → UInt32
@[extern "lean_corelogs_LOG_LOCAL0"] opaque LOG_LOCAL0 : Unit → UInt32
@[extern "lean_corelogs_LOG_LOCAL1"] opaque LOG_LOCAL1 : Unit → UInt32
@[extern "lean_corelogs_LOG_LOCAL2"] opaque LOG_LOCAL2 : Unit → UInt32
@[extern "lean_corelogs_LOG_LOCAL3"] opaque LOG_LOCAL3 : Unit → UInt32
@[extern "lean_corelogs_LOG_LOCAL4"] opaque LOG_LOCAL4 : Unit → UInt32
@[extern "lean_corelogs_LOG_LOCAL5"] opaque LOG_LOCAL5 : Unit → UInt32
@[extern "lean_corelogs_LOG_LOCAL6"] opaque LOG_LOCAL6 : Unit → UInt32
@[extern "lean_corelogs_LOG_LOCAL7"] opaque LOG_LOCAL7 : Unit → UInt32
@[extern "lean_corelogs_LOG_ALERT"] opaque LOG_ALERT : Unit → UInt32
@[extern "lean_corelogs_LOG_CRIT"] opaque LOG_CRIT : Unit → UInt32
@[extern "lean_corelogs_LOG_ERR"] opaque LOG_ERR : Unit → UInt32
@[extern "lean_corelogs_LOG_WARNING"] opaque LOG_WARNING : Unit → UInt32
@[extern "lean_corelogs_LOG_NOTICE"] opaque LOG_NOTICE : Unit → UInt32
@[extern "lean_corelogs_LOG_INFO"] opaque LOG_INFO : Unit → UInt32
@[extern "lean_corelogs_LOG_DEBUG"] opaque LOG_DEBUG : Unit → UInt32
@[extern "lean_corelogs_LOG_PID"] opaque LOG_PID : Unit → UInt32
@[extern "lean_corelogs_SIGILL"] opaque SIGILL : Unit → UInt32
@[extern "lean_corelogs_SIGTRAP"] opaque SIGTRAP : Unit → UInt32
@[extern "lean_corelogs_SIGABRT"] opaque SIGABRT : Unit → UInt32
@[extern "lean_corelogs_SIGBUS"] opaque SIGBUS : Unit → UInt32
@[extern "lean_corelogs_SIGFPE"] opaque SIGFPE : Unit → UInt32
@[extern "lean_corelogs_SIGUSR1"] opaque SIGUSR1 : Unit → UInt32
@[extern "lean_corelogs_SIGSEGV"] opaque SIGSEGV : Unit → UInt32
@[extern "lean_corelogs_SIGUSR2"] opaque SIGUSR2 : Unit → UInt32
@[extern "lean_corelogs_SIGALRM"] opaque SIGALRM : Unit → UInt32
@[extern "lean_corelogs_SIGSTKFLT"] opaque SIGSTKFLT : Unit → UInt32
@[extern "lean_corelogs_SIGURG"] opaque SIGURG : Unit → UInt32
@[extern "lean_corelogs_SIGXCPU"] opaque SIGXCPU : Unit → UInt32
@[extern "lean_corelogs_SIGXFSZ"] opaque SIGXFSZ : Unit → UInt32
@[extern "lean_corelogs_SIGVTALRM"] opaque SIGVTALRM : Unit → UInt32
@[extern "lean_corelogs_SIGPROF"] opaque SIGPROF : Unit → UInt32
@[extern "lean_corelogs_SIGWINCH"] opaque SIGWINCH : Unit → UInt32
@[extern "lean_corelogs_SIGIO"] opaque SIGIO : Unit → UInt32
@[extern "lean_corelogs_SIGPWR"] opaque SIGPWR : Unit → UInt32
@[extern "lean_corelogs_SIGSYS"] opaque SIGSYS : Unit → UInt32
@[extern "lean_decode_lossy_utf8"] opaque decodeLossyUTF8 (bytes : @& ByteArray) : String
@[extern "lean_corelogs_strerror"] opaque strerror (error : UInt32) : IO String
@[extern "lean_corelogs_openlog"]
opaque openlog (ident : @& String) (options facility : UInt32) : IO Unit
@[extern "lean_corelogs_syslog_text"]
opaque syslogText (priority : UInt32) (text : @& String) : IO Unit
@[extern "lean_corelogs_syslog_bytes"]
opaque syslogBytes (priority : UInt32) (bytes : @& ByteArray) : IO Unit
@[extern "lean_corelogs_closelog"] opaque closelog : IO Unit
@[extern "lean_corelogs_time"] opaque time : IO (UInt32 × UInt64)
@[extern "lean_corelogs_clock"] opaque clock : IO (UInt32 × UInt64 × UInt64)
@[extern "lean_corelogs_gmtime"] opaque gmtime (seconds : UInt64) : IO (Option TimeFields)
@[extern "lean_corelogs_localtime"] opaque localtime (seconds : UInt64) : IO (Option TimeFields)
@[extern "lean_corelogs_mktime"] opaque mktime (fields : @& Array Int32) : IO Int64
@[extern "lean_corelogs_langinfo"] opaque langinfo (item capacity : UInt32) : IO ByteArray
@[extern "lean_corelogs_lower_byte"] opaque lowerByte (byte : UInt32) : IO UInt32
@[extern "lean_corelogs_upper_byte"] opaque upperByte (byte : UInt32) : IO UInt32
@[extern "lean_corelogs_uname"] opaque uname : IO (UInt32 × String)
@[extern "lean_corelogs_prctl"] opaque prctl : IO Int
@[extern "lean_corelogs_open"] opaque openFile (path : @& String) (flags mode : UInt32) : IO Int
@[extern "lean_corelogs_close"] opaque close (fd : UInt32) : IO Int
@[extern "lean_corelogs_fstat"] opaque fstat (fd : UInt32) : IO (Option (Array Nat))
@[extern "lean_corelogs_winsize"] opaque winsize (fd : UInt32) : IO (UInt32 × Nat × Nat)
@[extern "lean_corelogs_flock"] opaque flock (fd operation : UInt32) : IO Int
@[extern "lean_corelogs_seek"] opaque seek (fd : UInt32) (offset : Int64) (whence : UInt32) : IO Int
@[extern "lean_corelogs_write"]
opaque write (fd : UInt32) (bytes : @& ByteArray) (offset : USize) : IO Int
@[extern "lean_corelogs_random"] opaque random (size : UInt32) : IO (UInt32 × ByteArray)
@[extern "lean_corelogs_rtmin"] opaque rtmin : IO UInt32
@[extern "lean_corelogs_rtmax"] opaque rtmax : IO UInt32

end LeanSudo.Sys.Prim.CoreLogs
