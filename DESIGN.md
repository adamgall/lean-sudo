# lean-sudo — design and module contracts

Lean 4, with the toolchain pinned in `lean-toolchain`; no Mathlib or Batteries.
The compatibility reference is sudo.ws 1.9.17p2. Proofs establish the properties
below of pure Lean functions, not correctness of the OS, FFI, or IO orchestration.

## Architecture: verified functional core, imperative shell

```text
argv, environment, NSS identities, filesystem/clock facts
sudo.conf, nsswitch.conf, sudoers files, SSSD attributes, group-provider answers
                         │
                         ▼
Main → Shell ── Context ──► Core.decide ──► Decision (auth, logs, action)
         │                    │
         │              Parser / Policy / Env / Timestamp / Cli
         ▼
Sys.* → C / PAM → authentication, timestamp locks, execution or sudoedit
         │
         ├─ local event/I/O logs or Sys.LogSrv → framed TCP/TLS log server
         └─ Sys.Intercept → privileged broker → refreshed facts → Intercept.decide
                              ▲                                  │
                              └── seccomp/ptrace or sudo DSO ────┘
```

`Core.decide : Context → Decision` is total and pure. It returns an authentication
requirement, not proof that PAM has succeeded: the trusted shell must satisfy it
before executing the action. The shell preserves authorization-time settings and
target facts separately from post-lookup privilege Defaults. It gathers rooted
command identity, descriptors, digests, regex and group facts; chroot happens only
in the final command child, after policy, PAM and host NSS lookups.

`Nsswitch` selects ordered `files`/`sss` policies and return actions. `Sys.Sss`
copies libsss_sudo attributes; pure `Sss` converts them into policy. Group-provider
answers are exact `(user, group, answer)` facts, not replacements for Unix groups.
Only a provider return of 1 is affirmative. `%:` requires an affirmative fact;
ordinary groups also consult the provider under `always_query_group_plugin`.
Provider load/init failure cannot invent membership, but need not deny an
independent rule.

Front-end audit, approval and additional I/O plugins use sudo's public 1.22 ABI.
`SudoConf` retains located plugin declarations and options; `Sys.Plugins` builds
settings and command metadata from the verified decision. The native host loads
objects, validates their ABI, dispatches callbacks and relays stream data. It does
not evaluate policy. Approval checks run only after successful policy/authentication;
`approval_only_restricts` and `denied_never_approved` make the conjunction explicit.
Audit plugins observe policy/approval/front-end outcomes; I/O plugins open only
after approval. Close receives the actual command wait status or execution error.
External policy plugins remain refused: lean-sudo itself supplies the policy.
Enforced intercepted commands repeat policy audit, approval and front-end audit;
log-only interception emits only the front-end audit. A private bounded socket
dispatches these callbacks from the forked Lean broker back to the original host,
preserving audit/approval state and the original I/O plugin vectors and session.
An absent or malformed affirmative reply cannot authorize a subcommand.

The interception broker retains the original principals and selected root and
refreshes command facts for each exec. Private reply sockets require affirmative
Lean authorization; malformed or absent replies cannot allow execution.
`intercept_authenticate` rechecks timestamps and authenticates under the record
lock. `log_subcmds` alone logs without a second authorization check; subcommand
environments are preserved. Trace mode skips the initially authorized exec and
can verify executable/arguments/environment before the new image runs. Its
verification retains sudo's relative-script/chroot label limitations. The DSO
backend uses `/usr/libexec/sudo/sudo_intercept.so`, bootstrap sockets, a random
128-bit token and native-endian length-prefixed protobuf messages. Neither backend
is a sandbox.

Remote logging replaces local I/O files when `log_servers` is configured. The
Lean client fails over initial connection establishment, not an established
session or malformed handshake. It validates server messages and durable commit
positions; I/O sessions send exit and await final commit, audit-only sessions
close without exit. Event setup uses `ignore_logfile_errors`; I/O setup/streaming
uses `ignore_iolog_errors`. Brokers queue encoded events to the original privileged
relay, which alone owns TCP/TLS state. The C transport bounds DNS/connect/TLS/I/O
by `log_server_timeout`, honors keepalive, and loads OpenSSL 3 with TLS ≥1.2 and
peer verification unless explicitly disabled.

The C shim and IO shell are trusted, not formally verified. PAM is dynamically
loaded from `libpam.so.0`; SSSD, group providers, gzip and TLS also use runtime
libraries. C implements credential changes, descriptors, relays and transports;
it does not interpret sudoers policy. Bindings are not one-to-one: `c/core.c`,
for example, serves both `Sys.Core` and `Sys.Pam`.

Gettext loading accepts installed locale/catalog data only through root-owned,
non-group/world-writable resolved paths and ancestors. Message catalogs use
`/usr/share/locale` and Ubuntu's `locale-langpack` fallback; `LANGUAGE` overrides
non-C message locales. Translation is a presentation boundary; log reasons use
separate `sudoers_locale` (C by default). Explicit prompts/messages remain literal,
and missing translations preserve English.

## Module map

Paths below are relative to `LeanSudo/` unless otherwise marked. Each row names
one source module; the C table also lists shared headers.

| Module | Purpose |
|---|---|
| `Cli.lean` | Pure sudo/sudoedit option scanner, diagnostics, help/version and shell escaping. |
| `CliProofs.lean` | Operand, mode, warning and shell-escaping invariants. |
| `Core/Types.lean` | Context, authentication, execution/edit plans, logging and decision contracts. |
| `Core.lean` | Pure decision, failure classification, authentication requirements and plans. |
| `CoreProofs.lean` | Authorization, identity, environment, root-selection and event-classification proofs. |
| `Env.lean` | Environment rebuild, explicit assignments, file sources and PAM merge. |
| `EnvProofs.lean` | Environment provenance, uniqueness and conditional protected-binding proofs. |
| `EventLog.lean` | Text/JSON accept, reject, alert and exit formatting and auth-failure predicates. |
| `I18n.lean` | GNU MO parsing, plural expressions, fallback and safe formatting. |
| `I18n/Render.lean` | Catalog-based diagnostic presentation without changing policy data. |
| `I18n/Load.lean` | Trusted locale/catalog discovery and separate message/log translation. |
| `Insults.lean` | Upstream insult collection and bounded selection. |
| `Intercept.lean` | Pure subcommand authorization with retained identities and environment. |
| `IoLog.lean` | Stream plans, sequence/path expansion, metadata and timing formatting. |
| `LogSrv.lean` | Pure sudo log-server protobuf codec and bounded round-trip proofs. |
| `Nsswitch.lean` | Ordered files/SSSD source parsing, validation and return-action selection. |
| `Policy/Types.lean` | Principals, requests, settings, command/root facts and judgements. |
| `Policy/Defaults.lean` | Typed Defaults application and scope resolution. |
| `Policy/Eval.lean` | Alias/list, user/host/run-as/command matching and candidate evaluation. |
| `Policy/List.lean` | Sudo privilege-list rendering and alias expansion. |
| `Policy/Proofs.lean` | Candidate provenance, last-match, negation, auth and rooted-selection proofs. |
| `Prompt.lean` | Sudo password-prompt percent expansion. |
| `Shell.lean` | Trusted sudo orchestration: facts, PAM, locks, logging, broker callbacks and execution. |
| `Sss.lean` | SSSD attribute conversion, filtering and sudoOrder/negation handling. |
| `SudoConf.lean` | sudo.conf paths/settings, located plugin declarations and built-in bypass validation. |
| `Sudoedit.lean` | Descriptor-based file preparation, editor execution and checked copy-back. |
| `Sudoedit/Check.lean` | Pure editor selection, separator, temporary-file and write-back checks. |
| `Sudoers/Ast.lean` | Located sudoers syntax, aliases, Defaults, tags and command options. |
| `Sudoers/Parser.lean` | Sudoers parser, diagnostics and successful-parse invariants. |
| `Sudoers/Load.lean` | Include resolution, ordering and source ownership/mode checks. |
| `Sys/Core.lean` | Identity, filesystem, terminal, environment, event logging and mail bindings. |
| `Sys/Edit.lean` | Credential-scoped descriptor-relative sudoedit worker operations. |
| `Sys/Exec.lean` | Checked execution specification and command supervisor bindings. |
| `Sys/Extra.lean` | System matching/audit oracles and root-containment helpers. |
| `Sys/GroupPlugin.lean` | Sudo group-provider configuration, load/query/cleanup bindings. |
| `Sys/Intercept.lean` | Broker request contract and scoped monitor lifecycle. |
| `Sys/IoLog.lean` | Local I/O session allocation, metadata and stream initialization. |
| `Sys/LogSrv.lean` | Remote session protocol, failover, relay callbacks and commit validation. |
| `Sys/Lookup.lean` | Credential-scoped batched path inspection and executable-bit criterion. |
| `Sys/Pam.lean` | PAM transaction/conversation configuration, lifecycle and diagnostics. |
| `Sys/Plugins.lean` | Front-end plugin metadata, lifecycle bindings and restriction-only approval theorem. |
| `Sys/Sss.lean` | SSSD defaults/user-rule attribute-query binding. |
| `Sys/Timestamp.lean` | Sudo-compatible record locking, storage, process identity and clock IO. |
| `Timestamp.lean` | Timestamp scopes, sudo v2 codec, bounded scanner, validity and update proofs. |
| `Util/Glob.lean` | Pure pathname-aware glob matcher and literal/star proofs. |
| `Util/Sha2.lean` | Pure SHA-224/256/384/512 and digest dispatch. |
| `Visudo/Core.lean` | Pure visudo options, semantic checks and editor-input helpers. |
| `Visudo/Sys.lean` | Visudo editor, record-lock, temporary-file and metadata bindings. |
| root `LeanSudo.lean` | Library umbrella importing the implementation and proof modules. |
| root `Main.lean` | Delegates sudo/sudoedit startup to `Shell.run`. |
| root `Visudo.lean` | Visudo check/edit/export orchestration and installation. |
| root `lakefile.lean` | Lean targets, shim compilation/linking and shared-header dependencies. |
| root `scripts/AxiomAudit.lean` | Audits all imported LeanSudo declarations for nonstandard axioms. |

| C source/header | Purpose |
|---|---|
| `c/core.c` | NSS/filesystem/terminal/log/mail primitives and dynamically loaded PAM conversation. |
| `c/edit.c` | Privilege-dropped sudoedit workers and descriptor reads/writes/restoration. |
| `c/exec.c` | Credential transitions, exec, pty/pipe relay, signals, deadlines and child setup. |
| `c/groupplugin.c` | Sudo group-provider ABI validation, initialization, query and cleanup. |
| `c/plugins.c`, `c/plugins.h`, `c/sudo_plugin.h` | Public sudo plugin ABI, dynamic loader, callbacks, lifecycle and execution-relay bridge. |
| `c/intercept.c` | Privileged broker, private request/reply transport and monitor lifecycle. |
| `c/intercept_trace.c` | Linux seccomp/ptrace exec monitor and optional post-exec verification. |
| `c/intercept_dso.c` | System sudo-intercept DSO bootstrap/authenticated protobuf transport. |
| `c/iolog.c` | Local plain/gzip streams, sequence locking, timing and password filtering. |
| `c/logsrv.c` | Deadline-bounded framed TCP/OpenSSL transport and relay/broker queue bridge. |
| `c/lookup.c` | Permanently credential-dropped child stat batches without policy selection. |
| `c/sss.c` | libsss_sudo dynamic ABI and checked attribute copying. |
| `c/sys.c` | Domain/interface/netgroup/regex/glob/hostname/audit system oracles. |
| `c/ts.c` | Secure timestamp descriptors, clocks, byte-range locks and positional IO. |
| `c/visudo.c` | Editor process, record locks, reusable temporary files and owner/mode operations. |
| `c/intercept.h` | Shared broker/trace monitor interface. |
| `c/intercept_dso.h` | DSO bootstrap, environment and service lifecycle interface. |
| `c/logsrv.h` | Framed transport, I/O relay and broker queue interface. |
| `c/locale_scope.h` | Thread-local sudoers locale enter/leave interface. |

## Sys API contract

Names in `Sys.Core`, `Sys.Pam`, `Sys.Exec`, `Sys.Timestamp` and `Sys.Extra`
are in `LeanSudo.Sys`; the other interfaces below use their named subnamespace.
The signatures below omit FFI borrowing annotations (`@&`) and private raw
bindings. Numeric widths are intentional: public wrappers often use `Nat`, while
descriptors and some raw-facing APIs use `UInt32`. Errors are API-specific:
`Option` can represent missing facts, PAM returns status codes, and IO failures
usually throw `IO.Error`; there is no universal “all failures throw” contract.

### Core

`Passwd` has `name : String`, `uid gid : Nat`, `gecos home shell : String`.
`FileStat` has `dev ino mode uid gid size rdev : Nat`; `mode` includes file type
bits, tested by `FileStat.isReg`, `isDir`, and `isLnk`.

```lean
getuid, geteuid, getgid, getegid : IO Nat
setUid : UInt32 → IO Unit
getgroups : IO (List Nat)
getpwnam : String → IO (Option Passwd)
getpwuid : Nat → IO (Option Passwd)
getgrnam : String → IO (Option GroupInfo)
getgrgid : Nat → IO (Option GroupInfo)
getgrouplist : String → Nat → IO (List Nat)
validShells : IO (Array String)
gethostname, getcwd, architecture : IO String
isatty : UInt32 → IO Bool
ttyname : UInt32 → IO (Option String)
environ : IO (List (String × String))
stat, lstat : String → IO (Option FileStat)
realpath : String → IO (Option String)
access : String → UInt32 → IO Bool
readFileFollow : String → IO (FileStat × String)
openCommand, openReadOnly : String → IO (Nat × FileStat)
closeDescriptor : UInt32 → IO Unit
listDir : String → IO (List String)
syslog : String → String → String → IO Unit
syslogBytes : String → String → ByteArray → Bool → IO Unit
writeStderr : String → IO Unit
umask : UInt32 → IO UInt32
unixTime : IO Nat
noNewPrivs : IO Bool
terminalColumns : UInt32 → IO Nat
terminalSize : IO (Nat × Nat)
utcOffset : IO Int
createAdminFlag : String → Nat → Nat → List Nat → IO Unit
logTime : Bool → String → IO String
eventTime : Bool → String → IO EventLog.Time
eventUuid : IO String
appendLog, appendJson : String → String → IO Unit
signalName : UInt32 → IO String
sendMail : String → Array String → String → IO Unit
```

Sudoers loading follows symlinks and checks the opened regular file; it is not
an O_NOFOLLOW policy. `openCommand` pins the executable; `openReadOnly` permits
checking opened-file metadata before reading. Environment entries without `=` or
valid UTF-8 are dropped. `appendJson` appends members to sudo's pretty JSON object,
not JSON lines. The module also exposes a no-follow reader for callers that need
that distinct primitive; it is not the sudoers loader contract.

### Pam

`PamHandle` is an external-object-backed type with finalizer cleanup. `ConvConfig`
fields are `useStdin nonInteractive visiblepw override pwfeedback : Bool := false`,
`prompt : String := "Password: "`, and `timeout : Nat := 0`.

```lean
pamStart : String → String → ConvConfig → String → Option String → IO PamHandle
pamConfigure : PamHandle → Bool → Bool → Bool → String → String → String → IO Unit
pamLecture : PamHandle → String → IO Unit
pamLectured : PamHandle → IO Bool
pamAuthenticate, pamAcctMgmt, pamChauthtok : PamHandle → IO Int
pamSetcred : PamHandle → Bool → IO Int
pamOpenSession, pamCloseSession : PamHandle → IO Int
pamSetUser : PamHandle → String → IO Int
pamGetEnv : PamHandle → IO (List (String × String))
pamStrerror : PamHandle → Int → IO String
pamEnd : PamHandle → Int → IO Unit
pamAvailable : IO Bool
pamLastConvError : PamHandle → IO (Option String)
pamInterrupted : PamHandle → IO UInt32
```

`pamStart` arguments are service, user, conversation, remote user, tty;
`pamConfigure` takes silent/sessionSilent/bell and askpass/rhost/promptUser.
Status 0 is PAM success. `pamEnd` is idempotent; authentication checks `PAM_USER`
against the requested account. Conversation errors and captured SIGINT/SIGQUIT
are separate from PAM status. Askpass runs as the invoker; the original environment
remains available during authentication, before command-environment filtering.

### Exec

```lean
structure ExecSpec where
  path : String
  argv : Array String
  env : Array String
  uid : Nat
  gid : Nat
  groups : Array Nat
  cwd : Option String
  umask : Nat
  usePty : Bool
  background : Bool
  closeFrom : Nat := 3
  cwdOptional : Bool := false
  timeout : Nat := 0
  noexecFile : Option String := none
  apparmorProfile : Option String := none
  rlimits : Array (String × String) := #[("rlimit_core", "0,0")]
  utmpUser : Option String := none
  execFd : Option Nat := none
  execBackground : Bool := false
  staySetuid : Bool := false
  chroot : Option String := none
inductive ExitStatus where
  | exited (code : Nat)
  | signaled (sig : Nat)
initializeProcess (disableCoredump : Bool := true) : IO Unit
lastDumpedCore : IO Bool
runCommand : ExecSpec → IO ExitStatus
exitWith : ExitStatus → IO α
```

`Exec.check` requires an absolute path, nonempty argv, NUL-free strings, IDs below
the unchanged-ID sentinel, umask ≤0777, closeFrom in 3..0x7fffffff, bounded timeout
and private executable descriptors. Child setup marks fds close-on-exec, optionally
chroots, drops/verifies credentials, applies cwd/umask and executes. `staySetuid`
retains the invoking real UID and all GIDs while effective/saved UID use the target;
normal mode uses the target IDs. Optional login cwd failure warns; required cwd
failure aborts. The supervisor relays signals/job control, enforces deadlines and
keeps PAM alive through background command completion. `exitWith` clamps exit codes
above 255 rather than wrapping success.

### Timestamp

```lean
structure TimestampConfig where
  directory : String := "/run/sudo/ts"
  uid : Nat
  ownerUid : Nat := 0
  ownerGid : Nat := 0
structure TimestampKey where
  scope : Timestamp.Scope
  lockScope : Timestamp.Scope
  sid : Nat
  authUid : Nat
bootTimeNanos, getsid, getppid : IO Nat
processStartTime : Nat → IO (Option Nat)
ttyDevice : IO (Option Nat)
stateMarker : String → Nat → Bool → IO Bool
readTimestamp : TimestampConfig → TimestampKey → IO (List Timestamp.Record)
withTimestampFile (config : TimestampConfig) (key : TimestampKey)
    (f : List Timestamp.Record → IO (Option Timestamp.Record × α))
    (report : String → IO Unit := fun _ => pure ()) : IO α
invalidateTimestamp : TimestampConfig → Timestamp.Scope → IO Unit
removeTimestampFile : TimestampConfig → IO Unit
```

Default storage is `/run/sudo/ts/<uid>`, using sudo's v2 disk format and compatible
header/per-terminal-or-process byte-range locks, not a private serialized list.
Foreign records retain their offsets. Global tickets also use a short record lock
for status/update. `readTimestamp` is only a nonblocking snapshot; authentication
rechecks under the long-held lock. Cache IO errors are reported and treated as no
trusted cache, not as authorization; callback errors are not retried. An update
changes only the selected record. `-k` disables matching records across auth UIDs;
`-K` unlinks the invoking UID's file. Process start time is nanoseconds converted
from `/proc` ticks, not raw field-22 jiffies; time uses CLOCK_BOOTTIME. Lecture
markers are separate from authentication records.

### Edit, Extra and Lookup

In `Sys.Edit`, `Identity` contains `uid gid : UInt32`, `groups : Array UInt32`;
`Result` contains `name : String`, `value : UInt32`. `noneFd = 0xffffffff` also
means AT_FDCWD on input.

```lean
Edit.identity : Nat → Nat → List Nat → IO Edit.Identity
Edit.operation (who : Edit.Identity) (op : UInt32) (dir : UInt32 := Edit.noneFd)
    (path : String := "") (mask : Nat := 0o022) (suffixLen : Nat := 0) : IO Edit.Result
Edit.close : UInt32 → IO Unit
Edit.stat : UInt32 → IO (Array Nat)
Edit.read : UInt32 → IO ByteArray
Edit.write : UInt32 → ByteArray → ByteArray → IO Unit
Edit.setTimes : UInt32 → UInt64 → UInt64 → IO Unit
Edit.clock : IO UInt64

domainName : IO (Option String)
interfaceAddresses : IO (Array (String × String))
inNetgroup : String → Option String → Option String → Option String → IO Bool
regexMatches (pattern text : String) (locale : String := "C") : IO Bool
globPaths (pattern : String) (locale : String := "C") : IO (List String)
canonicalHostname : String → IO (Except String String)
auditCommand : String → String → Bool → IO Bool
commandLookupRoot : Option String → Option String
withinRoot : String → String → Bool
rootPathEscapes : String → String → IO Bool

Lookup.executable : FileStat → Bool
Lookup.inspectPaths : Array String → Nat → Nat → Array Nat → IO (Array (Option FileStat))
```

Edit operations run in permanently privilege-dropped workers; callers own returned
descriptors. Write receives new bytes and the original snapshot for attempted
restoration on failure. Lookup uses one credential-scoped child per batch, retains
one stat result per path and rejects malformed/incomplete replies. Its executable
criterion is regular-file plus any execute bit, not `access(X_OK)`. Regex/glob use
sudoers locale. Audit unavailability is a successful no-op; an actual audit failure
returns false. Root containment uses path-component boundaries; `CHROOT=*` without
an override means host lookup, not a directory called `*`.

### IoLog and LogSrv

```lean
IoLog.open : LeanSudo.IoLog.Plan → LeanSudo.IoLog.Metadata → String → IO (Option String)
LogSrv.endpoint : String → Option (String × String × Bool)
LogSrv.accept : Settings → EventLog.Details → Option LeanSudo.IoLog.Plan → IO Unit
LogSrv.event (st : Settings) (details : EventLog.Details) (reason : String)
    (alert : Bool := false) : IO Unit
LogSrv.subcommand : EventLog.Details → Option String → IO Unit
LogSrv.finish (exitValue : Nat) (signal : String) (dumpedCore : Bool)
    (error : String := "") : IO Unit
LogSrv.close, LogSrv.poll : IO Unit
LogSrv.subcommandWire : ByteArray → IO Unit
LogSrv.ioEvent : UInt32 → ByteArray → UInt32 → UInt32 → IO Unit
```

Local open creates all selected files before execution, returning the session path;
errors throw unless the plan ignores them. Remote callbacks run in the privileged
relay, not the command child; `close` also detaches the broker queue. Endpoint
syntax supports bracketed IPv6 and `(tls)`, with default ports 30343/30344.

### Sss, GroupPlugin and Intercept

```lean
Sss.query : UInt32 → String → IO (Array LeanSudo.Sss.Rule × Array LeanSudo.Sss.Rule)
GroupPlugin.splitConfig : String → String × Array String
GroupPlugin.load : String → IO (Option GroupPlugin.Handle)
GroupPlugin.query : GroupPlugin.Handle → String → String → IO Bool
GroupPlugin.close : GroupPlugin.Handle → IO Unit

structure Intercept.Request where
  command : String
  cwd : String
  argv : Array String
  env : Array String
  pid : UInt32
  setid : Bool
Intercept.withMonitor (trace verify logOnly : Bool)
    (check : Intercept.Request → IO Bool) (action : IO α) : IO α
```

SSSD queries global defaults then user rules using the returned domain; rule order
is retained. Unavailable library/transport yields no rules for that query;
malformed data, invalid UTF-8 and other server failures throw rather than returning
partial rules. Group configuration splits only on spaces/tabs; relative libraries
resolve under `/usr/libexec/sudo`. Handles have explicit and finalizer cleanup.
Intercept requests deliberately contain no principal identities. `withMonitor`
brackets the action with broker start/stop, including exceptional exits.

## Verified properties (current theorem targets)

These are conditional statements over supplied facts, not claims that all IO is
proved. Names are unqualified within the module named in each item.

1. **Default deny and matching** (`Policy/Proofs`): `evaluate_nil` denies an empty
   policy; `evaluate_no_user_match` denies when every user-spec user list fails.
   `evaluate_sound` gives a member user/host/command spec satisfying `SpecMatches`.
   For `isRunCmd = true`, `evaluate_sound_run` additionally identifies the last
   candidate, `allow = true`, its user/host/run-as matches and positive command
   result. Listing instead uses positive candidates (`judgeListing_allow`); it is
   not covered by a universal last-command-wins claim.
2. **Negation**: `evaluate_last_deny` denies a run command when the last candidate's
   command result is `some false`; `evaluate_append_deny_all` denies a run command
   after appending `denyAllRule r.user.name`. Alias-denial theorems require their
   stated lookup/fuel and inner-match hypotheses.
3. **Authentication tags**: `evaluate_noauth_run` requires a successful run-command
   allow and `needsAuth = false`; the last positive candidate then has
   `passwd = some false`, or `passwd = none` with `authenticate = false`.
   `evaluate_noauth_listing` instead permits password policy `.never` or a positive
   candidate whose `specNeedsAuth` is false.
4. **Glob/parser**: `Glob.fnmatch_literal` equates matching with string equality
   when `hasMeta = false`; `fnmatch_star_pathname` says `*` matches exactly strings
   without `/`. `parse_wellFormed`, `parse_command_absolute`,
   `parse_digest_command_absolute` and `parse_regex_anchored` describe successful
   parser output, not semantic validity of arbitrary policies.
5. **Environment** (`EnvProofs`): successful `buildEnv` has unique keys
   (`buildEnv_nodup`) and documented provenance (`buildEnv_origin`).
   `buildEnv_reset_whitelist` requires reset mode and either no SETENV or no extra
   variables. `buildEnv_delete_respected` and `buildEnv_no_LD` allow trusted
   files/PAM and reset-mode whitelisting; they do not ban every LD variable.
   `buildEnv_securePath` requires no SETENV and compatible PAM writes;
   `buildEnv_sudo_vars` requires `BindingSafe` for each protected binding.
6. **CLI** (`CliProofs`): successful parsing returns exactly the scanner operands
   (`parseArgs_command`), a suffix of input (`parseArgs_command_suffix`); an initial
   `--` leaves the rest unchanged (`parseArgs_dashdash`).
   `parseArgs_login_shell`, `parseArgs_askpass_stdin` and `parseArgs_edit` exclude
   the stated conflicting modes and require edit files/no environment overrides.
7. **Timestamp validity/storage** (`Timestamp`): `valid_sound` gives matching scope
   and auth UID, nonfuture time, non-disabled state and a nonzero finite timeout;
   `valid_timeout_strict` strengthens finite age to `< timeout * 10^9`.
   `lookup_invalidateScope` prevents a cache hit for the invalidated scope.
   `decodeEntry_encodeEntry` and `decode_encode` require representable entries or
   records. `scanStep_bounds` gives `offset + 4 ≤ next ≤ extent`;
   `scanStep_decoded` ties emitted entries to `decodeSlot`; `scan_sound` gives each
   scanned entry a bounded step origin. `scan_timespecs` characterizes the validity
   flags, not universal validity of scanned records. `LocatedEntry.authorized_sound`
   additionally requires successful `recordFor` and `valid`, and yields UID/scope,
   valid timespecs, global-or-matching SID, non-disabled/nonfuture time and strict
   finite age. `updateEntry_sound` binds updates to the locked scope and auth UID.
8. **Decision core** (`CoreProofs`): `exec_origin`/`edit_origin` require an execution
   action and produce a policy allow, correct mode/plan and successful environment
   construction. `deny_no_execution` excludes both actions on policy denial.
   `exec_noauth` gives `AuthExemption` when an exec decision has `.auth = .none`;
   it does not prove PAM success. `exec_identity` fixes UID to target, GID to the
   invoking real GID under stay-setuid or selected target GID otherwise, and groups
   to invoking or target groups according to preserve-groups. `exec_environment`
   fixes the plan's inputs and empty pre-PAM environment, not the final post-PAM
   bytes. `timestamp_update_allowed` implies policy allow and neither `-N` nor
   reset; `reset_never_waives_auth` requires `policyNeedsAuth = true`.
9. **Logging** (`CoreProofs`): `failureLog_ne_accept` says any returned failure log
   is not `.accept`; `policy_failure_ne_accept` says the same for a policy decision
   with `decisionFailure = some failure`. `policy_warning_no_mail` says a failure
   with `denial = false` sets decision mail to false. These distinguish accept from
   reject/alert without asserting that every failure emits a log.
10. **Interception and groups**: `Core.exec_intercept_matches_policy` binds the
    exec plan's interception flag to the deciding tag/Defaults and logSubcmds to
    settings. `Core.intercept_setid_no_exec` excludes exec for an allowed run request
    with interception enabled, set-id facts true and `interceptAllowSetid = false`.
    `Intercept.allowed_only_by_policy` requires enforcement true and yields a
    positive core policy judgement. `Core.group_plugin_requires_yes` requires a
    successful non-Unix group match and yields the exact affirmative context fact;
    `Policy.pluginGroupMatch_requires_yes` gives the corresponding request fact.
11. **Chroot and command lineage**: `Core.exec_chroot_selection` yields an allow,
    `chrootPermitted = true`, and plan root equal to `commandChroot`.
    `exec_user_chroot_requires_wildcard` requires effective `CHROOT=*` for an explicit
    caller root; `exec_selected_root` binds the plan to the selected root after
    wildcard filtering/home expansion. `edit_chroot_uses_defaults` and
    `edit_user_chroot_requires_wildcard` give the separate sudoedit rule.
    `Policy.evaluate_selection_origin` traces every selected command/path/argv/fd/
    refusal/set-id fact to `rootFacts`; `Core.exec_fd_is_pinned` traces descriptors
    to host or root facts. `Sys.commandLookupRoot_wildcard` and
    `withinRoot_boundary` prove wildcard removal and component-boundary containment.
12. **LogSrv codec**: `Wire.varint_uint64` requires `< 2^64`;
    `Wire.signed_unsigned32/64` require the respective signed ranges.
    `Wire.fields_bytes_roundtrip` requires tags 1..15 and payload length `< 2^64`.
    `time_roundtrip`/`commit_roundtrip` require int64 seconds/int32 nanoseconds
    (not normalized wall-clock nanoseconds). `logId_roundtrip`, `error_roundtrip`,
    `abort_roundtrip` require UTF-8 size `< 2^64`; `clientHello_roundtrip` requires
    size +11 below that bound. `accept_zero_roundtrip`, `exit_zero_roundtrip`,
    `io_stream_roundtrip` and `hello_capability_roundtrip` cover only their stated
    finite/zero families; the I/O theorem uses streams `Fin 5`, zero delay and
    bytes `[0,128,255]`, not arbitrary messages. `Wire.fieldsAux_reject_group`
    rejects protobuf group wire types; `Wire.varint_window_bounded` limits lookahead
    to ten bytes. There is no blanket all-message round-trip theorem.
13. **Other boundaries**: `Sudoedit.writeBack_sound` requires changed and checked;
    `tempSafe_sound` requires regular, owned, single-link facts.
    `Nsswitch.approveSources_supported_only` gives nonempty files/sss-only sources.
    `Sss.negativesLast_mem` preserves membership and
    `negativesLast_exclusion_suffix` puts exclusions last. `IoLog.plan_enabled`
    equates plan presence with stream enablement. `I18n.lookup_absent` preserves
    the original message when no entry exists.

## Fail-closed rules and compatibility differences

As stated in README's **Fail-closed by design**, where sudo.ws keeps a partial
policy, lean-sudo stops because a dropped line can be a `!` rule:

* A syntax error anywhere in the policy stops lean-sudo; sudo.ws reports it and
  continues with the rules it could parse.
* An insecure or unreadable include stops lean-sudo: an included file or
  `@includedir` directory that is world-writable, group-writable by a group other
  than root, or not owned by root, and an `@include` file that is missing or cannot
  be read. sudo.ws warns and skips them.
* Undefined aliases and alias cycles are errors (sudo warns), because a
  `!UNDEFINED` matching nothing would widen access.
* Invalid Defaults values (for example `timestamp_timeout=abc`) are errors, rather
  than falling back to defaults that could widen access.
* Non-UTF-8 command-line arguments are refused; non-UTF-8 environment entries are
  dropped.

The README's **Other differences from sudo.ws** are:

* Fractional `timestamp_timeout` is rounded down to whole seconds.
* Chroot lookup rejects host-prefixed canonical commands or parents escaping the
  selected root. It also avoids three upstream false “command not found” cases:
  losing a selected command when a later NSS source is empty, dropping privileges
  before a nested run-as group lookup, and expanding a tilde root after lookup.
* As in sudo.ws, ptrace interception does not authorize `execveat`; the DSO mode
  inherits dynamic-loader limitations. Interception is a policy aid, not a sandbox.

These rules do not impose a no-symlink include policy or require an included
path's spelling to be a “real directory”; loading follows symlinks and checks the
relevant file/directory metadata.

## Build

Pure Lean library/proofs/tests build on Linux and macOS. The C shim and executables
are Linux-only; use Docker from macOS. Lake's default targets are `LeanSudo`,
`sudo` and `visudo`; the explicit library target avoids building Linux executables.

```sh
lake build LeanSudo Tests               # library, proofs and compile-time #guard tests
lake env lean scripts/AxiomAudit.lean   # after building the library
lake build sudo visudo                 # native Linux executables
lake build smoke-core smoke-exec smoke-ts  # Linux FFI smoke executables
integration/build.sh                   # Docker Linux sudo/visudo → .lake/linux/
integration/run.sh --build              # Docker end-to-end suite
integration/run.sh reference            # same suite against sudo.ws
integration/run.sh --visudo .lake/linux/visudo
```

Lake builds the listed shim translation units with `cc`, PIC/O2, warnings as
errors, stack protection and fortification; all four shared headers participate
in object dependencies. Linking uses `-ldl -lutil`; optional runtime libraries
are dynamically loaded. The axiom audit checks every declaration defined in
imported `LeanSudo` modules, including private/generated definitions, and permits
only `propext`, `Quot.sound`, and `Classical.choice`. It rejects `sorryAx` and
`Lean.ofReduceBool`; it does not audit the test library or prove C/IO correctness.
