import LeanSudo.Policy.Types
import LeanSudo.Cli
import LeanSudo.Env
import LeanSudo.Timestamp
import LeanSudo.IoLog
import LeanSudo.Nsswitch
import LeanSudo.EventLog

namespace LeanSudo.Core

open LeanSudo.Sudoers

structure ResolvedCmd where
  path : String
  canonical : String
  argv0 : String
  args : List String
  deriving Repr, BEq, DecidableEq, Inhabited

structure Context extends Facts where
  progname : String
  opts : Cli.Options
  invoking : Principal
  host : String
  sudoers : Sudoers
  settings : Settings
  target : Principal
  targetGroup : Option GroupInfo
  listUser : Option Principal
  command : Option ResolvedCmd
  commandSetid : Bool := false
  userEnv : EnvList
  cwd : String
  userUmask : Nat
  ttyName : Option String
  now : Nat
  tsScope : Timestamp.Scope
  tsRecords : List Timestamp.Record
  tsSessionId : Nat := 0
  tsLockScope : Timestamp.Scope := .global
  timestampOwnerUid : Nat := 0
  timestampOwnerGid : Nat := 0
  longHost : String := ""
  submitHost : Option String := none
  wallTime : Nat := 0
  envFile : EnvList := []
  restrictedEnvFile : EnvList := []
  homes : List (String × String) := []
  selinuxEnabled : Bool := false
  mailerAvailable : Bool := false
  locatedSudoers : List Located := []
  policySources : List (Nsswitch.Source × List Located) := []
  policySettings : Option Settings := none
  policyTarget : Option Principal := none
  execFd : Option Nat := none
  root : Principal := { name := "root", uid := 0, gid := 0, groups := [], home := "/root", shell := "/bin/bash" }
  previousUser : Option Principal := none
  listColumns : Nat := 0
  validShells : List String := []
  invokingRealGid : Option Nat := none
  commandFoundInDot : Bool := false
  targetUnknownUid : Bool := false
  targetUnknownGid : Bool := false
  runasDefaultUser : Option Principal := none

inductive AuthReq where
  | none
  | required (authUser : Principal)
  deriving Repr, BEq, DecidableEq, Inhabited

structure RunPlan where
  envInput : EnvInput
  umask : Nat
  pamService : String
  pamSession : Bool
  pamSetcred : Bool
  cwd : Option String := none
  cwdOptional : Bool := false
  usePty : Bool := false
  closeFrom : Nat := 3
  timeout : Nat := 0
  noexecFile : Option String := none
  apparmorProfile : Option String := none
  rlimits : List (String × String) := []
  utmpUser : Option String := none
  iolog : Option IoLog.Plan := none
  execBackground : Bool := false
  chroot : Option String := none

structure ExecPlan extends RunPlan where
  path : String
  argv : List String
  uid : Nat
  gid : Nat
  groups : List Nat
  background : Bool
  execFd : Option Nat := none
  staySetuid : Bool := false
  intercept : Bool := false
  logSubcmds : Bool := false

structure EditPlan extends RunPlan where
  files : List String
  editors : List (List String)
  editUid : Nat
  editGid : Nat
  editGroups : List Nat
  fileUid : Nat
  fileGid : Nat
  fileGroups : List Nat
  follow : Bool := false
  checkdir : Bool := true
  policyFiles : List String := []
  editorSources : List String := []
  editorNotFound : String := ""
  editorPath : String := ""

inductive Action where
  | exec (plan : ExecPlan)
  | edit (plan : EditPlan)
  | print (stdout : String) (code : UInt32)
  | fail (stderr : String) (code : UInt32)
  | validate
  | resetTimestamp
  | removeTimestamp
  deriving Inhabited

structure LogLine where
  priority : String
  msg : String
  format : String := "sudo"
  reason : Option String := none
  event : EventLog.EventType := .accept
  raw : Bool := false
  commandReady : Bool := true
  lookupComplete : Bool := true
  runcwd : Option String := none
  runchroot : Option String := none
  deriving Repr, BEq, DecidableEq, Inhabited

inductive AuditEvent where
  | accept
  | reject (reason : String)
  deriving Repr, BEq, DecidableEq, Inhabited

structure Decision where
  auth : AuthReq
  action : Action
  updateTimestamp : Bool
  log : Option LogLine
  adminFlag : Option String := none
  mail : Bool := false
  audit : Option AuditEvent := none
  deriving Inhabited

end LeanSudo.Core
