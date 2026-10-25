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
settings and command metadata from the verified decision. `Sys.PluginHost` loads
objects, validates their ABI and sequences lifecycle calls in Lean.
`Sys.PluginCallbacks` dispatches conversations, environment hooks and events;
its `RelayHooks` adapter receives stream bytes and signalfd notifications.
ABI offsets and platform constants come from C `sizeof`/`offsetof` and macro
values, queried only at runtime; no module initializer invokes a platform extern.
Background-session re-exec preserves the original submission process's PID and
parent PID in plugin `user_info`, rather than reporting the helper's identity.
Approval checks run only after successful policy/authentication;
`approval_only_restricts` and `denied_never_approved` make the conjunction explicit.
Audit plugins observe policy/approval/front-end outcomes; I/O plugins open only
after approval. Close receives the actual command wait status or execution error.
External policy plugins remain refused: lean-sudo itself supplies the policy.
Enforced intercepted commands repeat policy audit, approval and front-end audit;
log-only interception emits only the front-end audit. The parent Lean event loop
dispatches callbacks directly, preserving audit/approval state and the original
I/O plugin vectors and session. A missing affirmative Lean result cannot
authorize a subcommand.
As in sudo 1.9.17p2 `exec_intercept.c`, policy/front-end audit acceptance failures
are notifications for intercepted commands, not vetoes. Approval's own audit
acceptance still vetoes on failure (`sudo.c:approval_check`), as do all three
acceptance stages for initial execution. List/validate audit acceptance failures
are notifications, matching `sudo.c:policy_list` and `policy_validate`.

The interception broker retains the original principals and selected root and
refreshes command facts for each exec. The parent Lean tracer and authenticated
DSO broker require affirmative Lean authorization; malformed requests fail closed.
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
| `Intercept/Seccomp.lean` | Seccomp instruction construction, byte encoding and syscall-trap theorem. |
| `Intercept/Registers.lean` | Native, compat and x32 register decoding and updates. |
| `Intercept/Protocol.lean` | DSO protobuf codec using the proved log-server wire primitives. |
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
| `Sys/Core.lean` | Identity/filesystem wrappers and helper-backed mail/admin operations. |
| `Sys/CoreLogs.lean` | Log safety, locking, UUID encoding, time and terminal orchestration. |
| `Sys/TimeFormat.lean` | Lean date directives over native time fields and locale text. |
| `Sys/Prim/CoreFacts.lean` | NSS retries, environment decoding and bounded filesystem reads. |
| `Sys/Prim/Posix.lean` | Runtime platform constants without native-host extern initialization. |
| `Sys/Edit.lean` | Credential-scoped descriptor-relative sudoedit worker operations. |
| `Sys/Exec.lean` | Checked execution specification and command supervisor bindings. |
| `Sys/Extra.lean` | Matching validation, locale scopes, native-result walking and audit transport. |
| `Sys/GroupPlugin.lean` | Group-provider ABI validation, path fallback, lifecycle and result acceptance. |
| `Sys/Intercept.lean` | Parent-owned monitor lifecycle, execution preparation and relay hooks. |
| `Sys/InterceptTrace.lean` | Tracee memory, ptrace event decisions, exec verification and detach. |
| `Sys/InterceptDso.lean` | Authenticated DSO clients, nonblocking broker and environment injection. |
| `Sys/IoLog.lean` | I/O directories, sequence locks, gzip lifecycle, filtering and relay hooks. |
| `Sys/LogSrv.lean` | Remote session protocol, failover, relay callbacks and commit validation. |
| `Sys/Lookup.lean` | Credential-scoped batched path inspection and executable-bit criterion. |
| `Sys/Pam.lean` | PAM lifecycle, Lean conversation, terminal/signalfd password loop and diagnostics. |
| `Sys/PamHelpers.lean` | Re-exec askpass, mailer and admin-flag helper plans and handlers. |
| `Sys/Plugins.lean` | Front-end metadata and restriction-only approval theorems. |
| `Sys/PluginHost.lean` | ABI validation, lifecycle/audit/approval sequencing and relay hooks. |
| `Sys/PluginCallbacks.lean` | Conversation, environment hooks and plugin event state machines. |
| `Sys/PluginUserInfo.lean` | User, terminal, group and resource-limit metadata collection. |
| `Sys/Sss.lean` | SSSD dynamic loading, query/error policy and checked attribute/result walking. |
| `Sys/Timestamp.lean` | Timestamp path checks, effective-UID scopes, locking and record IO. |
| `Timestamp.lean` | Timestamp scopes, sudo v2 codec, bounded scanner, validity and update proofs. |
| `Util/Glob.lean` | Pure pathname-aware glob matcher and literal/star proofs. |
| `Util/Sha2.lean` | Pure SHA-224/256/384/512 and digest dispatch. |
| `Visudo/Core.lean` | Pure visudo options, semantic checks and editor-input helpers. |
| `Visudo/Sys.lean` | Lean storage/editor orchestration and scoped signalfd cleanup. |
| root `LeanSudo.lean` | Library umbrella importing the implementation and proof modules. |
| root `Main.lean` | Delegates sudo/sudoedit startup to `Shell.run`. |
| root `Visudo.lean` | Visudo check/edit/export orchestration and installation. |
| root `lakefile.lean` | Lean targets, shim compilation/linking and shared-header dependencies. |
| root `scripts/AxiomAudit.lean` | Audits all imported LeanSudo declarations for nonstandard axioms. |

| C source/header | Purpose |
|---|---|
| `c/core.c` | Single-call identity, terminal-presence and umask primitives. |
| `c/prim_posix.c` | Allocation-free accessors for target-platform constants. |
| `c/prim_corefacts.c` | NSS, environment, directory and filesystem one-call primitives. |
| `c/prim_corelogs.c` | One-call calendar, locale-data, syslog and log-file primitives. |
| `c/prim_pam.c` | PAM ABI trampoline and one-call PAM/terminal/password-I/O primitives. |
| `c/prim_edit.c` | One-call file and descriptor-transfer primitives; workers and rollback are Lean. |
| `c/prim_exec.c` | One-call process/terminal primitives, native constants, startup signal block and pinned re-exec stub. |
| `c/prim_groupplugin.c` | Group-plugin function-pointer primitives and printf-to-Lean trampoline. |
| `c/prim_plugins.c`, `c/sudo_plugin.h` | Public plugin ABI, one-call primitives and Lean callback trampolines. |
| `c/prim_intercept.c` | Allowlisted single-call ptrace, bounded memory/socket/descriptor primitives and bounds-checked native ABI metadata; raw errno values are interpreted in Lean. |
| `c/prim_iolog.c` | One-call filesystem, zlib, regex, terminal and clock primitives. |
| `c/prim_logsrv.c` | Socket, polling, address lookup and OpenSSL call primitives. |
| `c/prim_lookup.c` | Native lookup constants; credentialed stat batches run in Lean helpers. |
| `c/prim_sss.c` | One-call libsss_sudo primitives and bounded native result accessors. |
| `c/prim_store.c` | Dynamic loading, allocation, native pointer/string and error primitives. |
| `c/sys.c` | One-call netgroup membership binding. |
| `c/prim_extra.c` | Matching, locale, address/interface, hostname and netlink primitives. |
| `c/prim_timestamp.c` | One-call filesystem, clock and process-identity primitives. |
| `c/visudo.c` | Single-call primitives, platform constants and bounded result/wait-status decoding. |
| `c/prim_visudo.c` | Native default executable-search path and lookup-error constants. |

## Trusted C boundary (target architecture)

A bug in C invalidates the proofs, so C is reduced to code that cannot be written
in Lean. Every C function must fall into exactly one of these categories; anything
else (parsing, formatting, protocol encoding, policy, sequencing, retry/fallback
logic, loops over data, state machines) is Lean.

1. **Primitive wrappers.** One system call or library call per function, arguments
   already validated in Lean, result or `errno` returned unchanged. The only control
   flow allowed is the error check and a bounded copy of the result into a Lean value.
   Native constants and structure layouts are exposed by scalar constant accessors;
   Lean never assumes architecture-specific flag values, sizes or offsets.
2. **Callback trampolines.** C entry points required by a C ABI (PAM conversation,
   sudo plugin callbacks, `libsss_sudo`, OpenSSL, zlib) that forward their arguments
   to a Lean closure and return its answer. `vsnprintf` for printf-style callbacks is
   the only formatting in C.
3. **The post-fork boundary.** A multithreaded process's forked child may only call
   async-signal-safe functions. The stub resolves `_Fork` in the parent and fails
   closed if unavailable, so no `pthread_atfork` handlers run. It clears
   close-on-exec on the descriptors Lean listed, moves the plan socket
   to descriptor 63 and immediately `fexecve`s the pinned lean-sudo binary
   (`/proc/self/exe`, opened `O_PATH|O_CLOEXEC` above descriptor 2 before runtime
   startup). The parent never holds an inheritable plan descriptor, so concurrent
   forks by PAM, NSS or plugins cannot capture it. The Lean-serialised plan travels
   over one end of an `AF_UNIX` socketpair created by the spawning process. If that
   process runs with a lowered effective UID, only the calling thread's effective UID
   is set to the saved UID around `socketpair` (raw per-thread `setresuid`, so no
   other thread gains it), and a failed restore terminates the process. Before
   reading any plan byte, dispatch requires descriptor 63 to be a socket whose
   `SO_PEERCRED` process is the helper's parent and whose credential UID (the
   creator's effective UID when the pair was made) equals the helper's effective
   UID. An unprivileged user can run the setuid binary with a socket of their own,
   even below a waiting sudo process, but that socket carries their own effective
   UID and is rejected. Only then are the parent PID, effective UID and protocol
   magic in the envelope checked and a registered helper selected. Unauthenticated
   helper arguments take the ordinary usage-error path. The fresh helper performs
   privilege changes and verification, chroot/cwd, limits, AppArmor and final exec
   through primitives. Mailer, askpass, sudoedit and lookup workers use this same
   transport.
   Background execution starts a fresh authenticated session helper with the
   original argv, environment, pinned cwd and a status pipe. The original process
   consumes signals without forwarding them and waits until command startup is
   acknowledged, or returns the session's failure status if it exits first.
   The helper owns the complete policy/PAM/plugin/log lifecycle and detaches its
   process group only at the command-execution boundary. There is no post-fork
   Lean continuation and no assumption that the runtime remains single-threaded.

The sole scoped exception is the timestamp `F_SETLKW` wait primitive. POSIX
interoperability requires the waiting lock to belong to sudo's own PID, and
`signalfd` consumption cannot interrupt a blocking `fcntl`. For one `F_SETLKW`
call in the calling thread, this primitive temporarily installs handlers for the
specified interrupt signals and unblocks those signals. Each handler only stores
its signal number in a `volatile sig_atomic_t`. The primitive restores the prior
mask and dispositions and returns the syscall result, saved errno and signal
number; Lean owns interruption policy and any retry. As in sudo.ws, inherited
`SIG_IGN` is temporarily overridden for these lock-interrupt signals, then restored.
There is an unavoidable check-to-syscall window: a signal delivered after the
stored-signal check but before `fcntl` enters the kernel can delay interruption
until the lock is granted, as in sudo.ws. The signal number remains recorded;
Lean then releases any acquired lock and falls back to authentication. The C
primitive never synthesizes `EINTR` for a signal received before the syscall.

Primitive signatures match the prototypes emitted by Lean: `BaseIO` returns the
bare value, while `IO` returns `IO.Result`. Scalar results are unboxed; products
and options use Lean constructors. Erased world arguments are absent from the C
signature. Native constants are obtained at runtime, never through module
initialization that would evaluate a Linux-only extern on another platform.

Every Docker Linux build runs `scripts/check-ffi.sh` after `lake build sudo visudo`.
It extracts the Lean extern prototypes from generated C, writes
`.lake/build/ffi/externs.h`, and force-includes that header while compiling every
`c/*.c` with `-Wall -Wextra -Werror`. Empty argument lists become `(void)` so
argument-count mismatches cannot hide behind C's unspecified-argument syntax.
The check also rejects externs without generated prototypes or definitions in C
or the installed Lean runtime, and non-static C functions without a Lean extern,
a caller in another C file, or a libc symbol to interpose. Runtime definitions and
libc interposition names are discovered from library symbol tables, not allowlists.

The same build then runs `scripts/check-c-boundary.sh`, a ratchet over
`scripts/c-budget.tsv`: every file in `c/` needs a budget entry, and neither its
line count nor its branch-statement count (`if`/`for`/`while`/`switch`/`do`) may
exceed it. Process creation (`fork`, `_Fork`, `clone`) is confined to
`c/prim_exec.c`, signal-disposition changes to `c/prim_exec.c` and the timestamp
lock primitive, and `pthread_create`, `system` and `popen` are forbidden. Raising a
budget is a deliberate, reviewed change to the trusted base.

Consequences: event loops (pty relay, signal relay via `signalfd`, job control, the
ptrace tracer, the I/O-log writer, the log-server client, the interception broker)
are Lean loops over `poll`/`read`/`write`/`waitpid`/`ptrace` primitives. Signals are
blocked in every thread before the runtime starts additional threads and consumed
through `signalfd`, except for the scoped timestamp-lock wait above. Seccomp BPF is built in
Lean as bytes. Structures crossing the boundary (plugin `command_info`, ptrace
register sets, timestamp records) are encoded and decoded in Lean.
Lean removes glibc's internal realtime signals from every execution mask, using
native kernel and libc realtime minima. Signal-action primitives return the raw
previous handler, flags and mask; Lean chooses ignore/default policy and restores
the complete disposition after job-control stops. Execution vector, group and poll
marshalling uses bounded heap allocations, and native structure access rejects
incorrect byte-array sizes. Background environment replacement occurs only in the
authenticated session helper, never in the spawning process.
Command helpers initialize the inherited locale after re-exec, before formatting
native errno diagnostics through thread-safe `strerror_r`.

## Sys API contract

Names in `Sys.Core`, `Sys.Pam`, `Sys.Exec`, `Sys.Timestamp` and `Sys.Extra`
are in `LeanSudo.Sys`; the other interfaces below use their named subnamespace.
The signatures below omit FFI borrowing annotations (`@&`) and private raw
bindings. Numeric widths are intentional: public wrappers often use `Nat`, while
descriptors and some raw-facing APIs use `UInt32`. Errors are API-specific:
`Option` can represent missing facts, PAM returns status codes, and IO failures
usually throw `IO.Error`; there is no universal “all failures throw” contract.

The Linux translation units share the `c/shim.h` inline result-marshalling helpers.
Credentialed helpers share Lean's `Helper.dropCredentials`: real/effective/saved
and filesystem IDs, the sorted supplementary-group multiset, and inability to
regain root are checked before filesystem work or exec. Command execution supplies
the separate real-UID/GID selection for `stay_setuid` and stages resource limits
around the drop.
Network and broker log frames share bounded framing, but retain their different
blocking, TLS and interruption semantics. Syslog policy and C mappings accept
sudo.ws's facilities: `authpriv`, `auth`, `daemon`, `user`, and `local0`–`local7`.

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
localCivilEpoch : Nat → IO (Option Int)
createAdminFlag : String → Nat → Nat → List Nat → IO Unit
logTime : Bool → String → IO String
eventTime : Bool → String → IO EventLog.Time
eventUuid : IO String
appendLog, appendJson : String → String → IO Unit
signalName : UInt32 → IO String
sendMail : String → Array String → String → IO Unit
```

Zone-less command time bounds are resolved individually with the system timezone
and `mktime(tm_isdst = -1)`, not the current UTC offset. The shell supplies the
resulting civil-time-to-epoch table to both matching and listing; a missing local
bound never authorizes a command. Startup removes the caller's `TZ` before this
conversion, including daylight-saving gaps and folds.

Sudoers loading follows symlinks and checks the opened regular file; it is not
an O_NOFOLLOW policy. `openCommand` pins the executable; `openReadOnly` permits
checking opened-file metadata before reading. Environment entries without `=` or
valid UTF-8 are dropped. `appendJson` appends members to sudo's pretty JSON object,
not JSON lines. The module also exposes a no-follow reader for callers that need
that distinct primitive; it is not the sudoers loader contract.

Log timestamps use the shared Lean `Sys.TimeFormat` formatter over decoded native
calendar fields and `nl_langinfo` locale data. Local timestamps retain
`%b %e %H:%M:%S` with optional ` %Y`; event UTC timestamps retain
`%Y%m%d%H%M%SZ`. Formatting preserves locale bytes until the original 64-byte
buffer limit is checked, then decodes UTF-8 lossily. Empty output or output of
64 bytes or more retains the existing timestamp-format error. C supplies only
calendar conversion, locale facts and bounded result marshaling.

### Pam

`PamHandle` owns Lean conversation/lifecycle state and an external native PAM
handle. Lean closes PAM in `finally`; the native finalizer only releases its
allocation and retained closure. `ConvConfig` fields are
`useStdin nonInteractive visiblepw override pwfeedback : Bool := false`,
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
PAM's C conversation entry point forwards raw message/response pointers to a
retained Lean closure and returns its answer. Lean validates the bounded message
count, reads native fields, allocates responses, and erases/frees failed responses.
Prompt selection, lecture state, stdin/tty/askpass selection, feedback editing,
deadlines and signal handling are Lean. The password loop consumes blocked signals
through signalfd and restores terminal attributes on exit. Native termios field
accessors validate buffers; Lean chooses every edit. Lean also walks PAM environment
vectors and builds NULL-terminated helper argument vectors.
Askpass, mail and admin-flag operations use authenticated helper plans; helpers
verify dropped credentials before touching invoker files or executing a program.
PAM messages, translated prompts and password responses cross the ABI as raw bytes;
askpass plans preserve those prompt bytes. The returned PAM user is decoded strictly
before comparing it with the requested account, so invalid UTF-8 cannot alias an identity.

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
restoreCoreLimit : IO Unit
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

`RelayHooks` composes plugin hooks before I/O logging and interception. Stream hooks
receive stdin/stdout/stderr/ttyin/ttyout identities; child hooks receive raw wait
statuses, and a spawn hook attaches the tracer before releasing the helper gate.
Stream approval stops at the first `false`; child-event `true` claims the event,
while `false` falls through to the next hook and then the supervisor. Event hooks
abort by throwing. A claimed ptrace stop must be resumed or deliberately retained
by its owning hook.
The Lean supervisor owns pty/nopty polling, job-control messages, timeouts, terminal
restoration, utmp records and child-error decoding. Hook failure kills and reaps the
command before resources are released.

The caller's core limit is restored before PAM credentials and session setup,
not over PAM's result in the command child. Explicit sudoers resource limits are
applied afterward; `!rlimit_core` leaves PAM's limit intact, while `!pam_session`
preserves the caller's limit. Ubuntu's systemd package installs
`/etc/security/limits.d/10-coredump-debian.conf`, which sets the root soft core
limit to zero.

Authentication-failure file events follow sudo.ws's combined log/mail gate.
When a usable mailer will report a policy denial, the redundant bad-password
event is omitted from both logfile and syslog; the diagnostic still goes to
stderr. Without that denial mail, `mail_badpass` can produce a file-only
authentication event even when the mailer is unavailable.
As in sudo.ws, the mailer's own outcome (exit status, early close of its input)
never changes sudo's diagnostics or exit status; only a failure to start the mail
helper is reported.

Background re-execution preserves the original caller's PID in acceptance syslog
records through `Sys.CoreLogs.setSyslogPidOverride`. Clearing that override at the
detach boundary restores the supervisor's PID for exit records. When PID output
is disabled, neither identity includes a PID. Lean retains each `openlog` identity
string through `closelog`, because libc borrows its storage.

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
Traversal and stale-file replacement keep the currently owned descriptor in an
`IO.Ref`, so exceptional cleanup closes the latest descriptor rather than a
pre-`try` snapshot. I/O-log directory traversal follows the same ownership rule.

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
IoLog.remote : UInt32 → Array String → IO Unit
IoLog.relayHooks : RelayHooks
LogSrv.endpoint : String → Option (String × String × Bool)
LogSrv.accept : Settings → EventLog.Details → Option LeanSudo.IoLog.Plan →
    (UInt32 → Array String → IO Unit) → IO Unit
LogSrv.event (st : Settings) (details : EventLog.Details) (reason : String)
    (alert : Bool := false) : IO Unit
LogSrv.subcommand : EventLog.Details → Option String → IO Unit
LogSrv.finish (exitValue : Nat) (signal : String) (dumpedCore : Bool)
    (error : String := "") : IO Unit
LogSrv.close, LogSrv.poll : IO Unit
LogSrv.withBroker : IO α → IO α
LogSrv.ioEvent : UInt32 → ByteArray → UInt32 → UInt32 → IO Unit
```

Local open creates all selected files before execution, returning the session path;
errors throw unless the plan ignores them. Remote callbacks run in the privileged
relay, not the command child; `close` also detaches the broker queue. Endpoint
syntax supports bracketed IPv6 and `(tls)`, with default ports 30343/30344.
`accept` receives `IoLog.remote` for password-filter initialization. `IoLog.relayHooks`
streams local/remote I/O and polls the server; the parent shell sends the final
exit/commit exchange. DNS resolution runs in the registered `logsrv-resolve` helper,
with its deadline, cleanup, framing and runtime-native address hints controlled by
Lean. Lean allocates receive buffers, builds the TLS SIGPIPE mask and sequences
pending-signal inspection around each TLS call; only newly pending SIGPIPE is
consumed with a nonblocking wait. Socket byte counts retain `ssize_t` width,
while TLS counts are checked against its native `int` ABI. Native transfers reject
out-of-bounds slices before pointer arithmetic or receive-buffer mutation.

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
resolve under `/usr/libexec/sudo`. Lean closes group-plugin handles in `finally`;
garbage collection never invokes plugin code. Each query owns a reentrant passwd
lookup buffer until the plugin returns, so plugin lookups cannot overwrite it.
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
   `lookup_invalidateScope` rejects a record projected from a disabled runtime slot;
   `invalidateScope_other` leaves nonmatching slots untouched, and `lookup_update_other`
   prevents a written record authorizing another key. `decodeEntry_encodeEntry` and
   `decode_encode` round-trip representable fixed-slot entries.
   `scanStep_bounds` gives `offset + 4 ≤ next ≤ extent`; `scanStep_decoded` ties emitted
   entries to `decodeSlot`, whose `decodeSlot_validity` characterizes raw timespec flags.
   `LocatedEntry.authorized_sound`
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
Runtime and visudo retain separate include walkers: runtime failures abort policy
loading, while visudo also tracks editable files and distinguishes errors from
warnings. Both use the same ownership checks and lexical directory-entry sorting.
Command capture shares descriptor-backed digest collection without merging the
host/root lookup choices; PAM transactions share configuration and cleanup.

## Build

Pure Lean library and proofs build on Linux and macOS. The C shim and executables
are Linux-only; use Docker from macOS. Lake's default targets are `LeanSudo`,
`sudo` and `visudo`; the explicit library target avoids building Linux executables.

Testing: the only tests are the Docker end-to-end suites in `integration/` (real
binaries, real system components, expectations checked against sudo.ws). Unit tests,
`#guard`/`#eval`/`example` checks, test-only hooks and mocks are not allowed; internal
properties are theorems.

```sh
lake build LeanSudo                    # library and proofs
lake env lean scripts/AxiomAudit.lean   # after building the library
lake build sudo visudo                 # native Linux executables
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
`Lean.ofReduceBool`; it does not prove C/IO correctness.
