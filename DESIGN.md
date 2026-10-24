# lean-sudo — design and module contracts

A drop-in replacement for `sudo` written in Lean 4 (toolchain pinned in
`lean-toolchain`, core Lean only — no Mathlib/Batteries), with the security-relevant
logic formally verified.

## Architecture: verified functional core, thin imperative shell

```
argv, environ ─┐
getpw*/getgr*  ├─► IO shell (Main.lean) ──► pure core (LeanSudo.Core.decide) ──► Decision
/etc/sudoers   ┘        │                         uses Parser, Policy, Env, Cli, Timestamp
                        ▼
              C shim (c/*.c): PAM, setres[ug]id, fork/execve/wait, pty, termios, stat
```

* Everything that decides *whether* and *how* a command runs is a total, pure Lean
  function with theorems about it (see "Verified properties").
* The IO layer only gathers facts, calls the pure core, and executes its decision.
* The C shim is the trusted computing base: small, no policy, one syscall concern per
  function. Each `c/<x>.c` file is owned by exactly one `LeanSudo/Sys/*.lean` module.
* PAM is `dlopen("libpam.so.0")`ed at runtime (Lean's bundled sysroot cannot link
  against system libpam, and there are no PAM headers on the build host — the shim
  declares the stable PAM ABI itself).

Gettext catalogs are optional. The shell activates only installed locales and loads
`sudo` / `sudoers` catalogs from `/usr/share/locale`, then Ubuntu's
`/usr/share/locale-langpack`, with `LANGUAGE` overriding the selected message locale
except in C. Every resolved catalog path and ancestor must be root-owned and not
group/world-writable. Translation occurs only at user-output boundaries: pure
decisions and audit/log data remain independent of the caller's locale. Log reasons
use the separate `sudoers_locale` (C by default). Explicit `passprompt` and
`badpass_message` values are literal; only compiled-in defaults are translated.
Absent catalogs preserve the original English bytes.

## Module map

| Module | Contents |
|---|---|
| `LeanSudo/Sudoers/Ast.lean` | sudoers AST (contract, frozen) |
| `LeanSudo/Policy/Types.lean` | `Principal`, `Request`, `Command`, `Settings`, `Judgement` (contract, frozen) |
| `LeanSudo/Sudoers/Parser.lean` | `parse : (file : String) → (text : String) → Except ParseError (List Located)` |
| `LeanSudo/Util/Glob.lean` | `fnmatch (pattern s : String) (pathname : Bool) : Bool` + proofs |
| `LeanSudo/Util/Sha2.lean` | pure SHA-224/256/384/512 over `ByteArray`, digest dispatch and output-length proofs; NIST known-answer tests in `Tests.Sha2` |
| `LeanSudo/Policy/Defaults.lean` | `resolveDefaults` (Defaults → `Settings`) |
| `LeanSudo/Policy/Eval.lean` | `evaluate : Sudoers → Settings → Request → Judgement`, matching |
| `LeanSudo/Policy/List.lean` | `sudo -l` rendering |
| `LeanSudo/Policy/Proofs.lean` | policy theorems |
| `LeanSudo/Cli.lean` | `parseArgs (argv0 : String) (args : List String) (env : List (String × String) := []) : ParseResult` (`warnings`, `result : Except Diagnostic Options`; getopt-style diagnostics carry the full argv[0]) |
| `LeanSudo/Env.lean` | `buildEnv` (command environment, sudo's env.c order: rebuild, then explicitly permitted `VAR=value`/`--preserve-env`, then PAM `env_merge`) + proofs |
| `LeanSudo/Prompt.lean` | `%u %U %h %H %p %%` prompt expansion |
| `LeanSudo/I18n.lean`, `LeanSudo/I18n/Render.lean` | pure GNU MO parsing, catalog fallback theorem, plural expressions, printf substitution and diagnostic presentation |
| `LeanSudo/I18n/Load.lean` | root-owned catalog/locale loading; message-locale precedence, Ubuntu langpack fallback, separate `sudoers_locale` log catalog |
| `LeanSudo/Timestamp.lean` | pure timestamp records, (de)serialisation, validity + proofs |
| `LeanSudo/IoLog.lean` | pure I/O stream plans (`plan_enabled`), sudo path escapes, base-36 sequence paths, legacy/JSON metadata and timing records |
| `LeanSudo/EventLog.lean` | pure sudo text wrapping and ordered JSON accept/reject/alert/exit formatting; `@cee:` syslog records, pretty logfile members and compact JSON lines |
| `LeanSudo/Sys/Core.lean` + `c/core.c` | users/groups/host/tty/stat/realpath/secure read/environ/syslog |
| `LeanSudo/Sys/Pam.lean` (+ `c/core.c`) | PAM handle + conversation (tty / `-S` stdin / `-n`) |
| `LeanSudo/Sys/Exec.lean` + `c/exec.c` | privilege drop, fork/execve/wait, signal relay, pty |
| `LeanSudo/Sys/Timestamp.lean` + `c/ts.c` | timestamp file storage, boot clock, session/process identity |
| `LeanSudo/Sys/GroupPlugin.lean` + `c/groupplugin.c` | sudo group-provider ABI loading (`dlopen`), version validation, init/query/cleanup; the shell supplies exact `(user, group, answer)` facts to pure policy matching |
| `LeanSudo/Sys/IoLog.lean` + `c/iolog.c` | fail-closed session creation, locked sequence allocation, owner/mode enforcement, plain/gzip streams, password-prompt filtering; pty and pipe relay hooks in `c/exec.c` |
| `LeanSudo/Core/Types.lean` | decision-core contract: `Context`, `Decision`, `ExecPlan`, `EditPlan`, `Action` |
| `LeanSudo/Core.lean`, `LeanSudo/CoreProofs.lean` | pure decision core (`decide`) + end-to-end theorems |
| `LeanSudo/Sudoers/Load.lean` | include resolution + file ownership/mode checks |
| `Main.lean`, `LeanSudo/Shell.lean` | `sudo` / `sudoedit` entry point; IO shell (gathers the `Context`, runs PAM, executes the `Decision`) |
| `LeanSudo/Sudoedit.lean`, `LeanSudo/Sudoedit/Check.lean`, `LeanSudo/Sys/Edit.lean` + `c/edit.c` | sudoedit: proved editor selection/copy-back checks; privilege-dropped file workers |
| `Visudo.lean`, `LeanSudo/Visudo/Core.lean`, `LeanSudo/Visudo/Sys.lean` + `c/visudo.c` | `visudo` entry point; pure CLI/checks; record locks, reusable temp files, owner/mode |
| `test/` | `Tests` library (`#guard` unit tests, checked by `lake build Tests`) and IO smoke executables |
| `scripts/AxiomAudit.lean` | checks every `LeanSudo` declaration uses only the standard axioms |
| `integration/` | Docker-based end-to-end suite (runs as real root in a container) |

## Sys API contract (Lean signatures)

All in `namespace LeanSudo.Sys`. Numeric ids are `Nat` on the Lean side, `uid_t`/`gid_t`
in C. Errors are raised as `IO.userError` with `strerror` text unless an `Option`
is returned.

### `LeanSudo.Sys.Core`
```lean
structure Passwd where
  name : String; uid : Nat; gid : Nat; gecos : String; home : String; shell : String
structure FileStat where
  dev : Nat; ino : Nat; mode : Nat  -- full st_mode incl. type bits
  uid : Nat; gid : Nat; size : Nat; rdev : Nat
def FileStat.isReg / isDir / isLnk : FileStat → Bool

getuid geteuid getgid getegid : IO Nat
getgroups : IO (List Nat)                       -- supplementary groups of this process
getpwnam : String → IO (Option Passwd)
getpwuid : Nat → IO (Option Passwd)
getgrnam : String → IO (Option GroupInfo)
getgrgid : Nat → IO (Option GroupInfo)
getgrouplist : (user : String) → (gid : Nat) → IO (List Nat)
gethostname : IO String
isatty : (fd : UInt32) → IO Bool
ttyname : (fd : UInt32) → IO (Option String)
environ : IO (List (String × String))           -- entries that are not valid UTF-8 or lack '=' are dropped
stat lstat : String → IO (Option FileStat)
realpath : String → IO (Option String)
access : (path : String) → (mode : UInt32) → IO Bool   -- X_OK etc, as real uid
/-- open with O_RDONLY|O_NOFOLLOW|O_CLOEXEC, fstat the *opened* fd, read it fully. -/
readFileNoFollow : String → IO (FileStat × String)
listDir : String → IO (List String)             -- names, excluding . and ..
syslog : (facility : String) → (priority : String) → (msg : String) → IO Unit
getcwd : IO String
writeStderr : String → IO Unit                   -- unbuffered
```

Group-provider membership is separate from NSS/Unix membership. The shell loads
`group_plugin` relative to `/usr/libexec/sudo` unless its path is absolute, passes
space/tab-separated arguments to the provider's version-1 ABI, and closes it after
collecting facts (with a finalizer for exceptional exits). Only a query return of
exactly `1` becomes an affirmative fact. `%:` atoms require that fact; ordinary
`%group`/`%#gid` atoms retain Unix membership and additionally consult it when
`always_query_group_plugin` is enabled. A loader/init error does not itself deny
independent rules, matching sudo.ws, but can never manufacture plugin membership.

### `LeanSudo.Sys.Pam`
```lean
opaque PamHandle : Type        -- NonemptyType-backed external object
structure ConvConfig where
  /-- `-S`: read from stdin instead of /dev/tty -/
  useStdin : Bool
  /-- `-n`: any prompt fails the conversation -/
  nonInteractive : Bool
  /-- expanded passprompt; replaces PAM's "Password: " style prompts when
  `override` is true or the PAM prompt is the generic one -/
  prompt : String
  override : Bool
  pwfeedback : Bool
  /-- seconds, 0 = none -/
  timeout : Nat
pamStart : (service : String) → (user : String) → ConvConfig → (ruser : String) → (tty : Option String) → IO PamHandle
-- each returns the raw PAM return code (0 = PAM_SUCCESS)
pamAuthenticate : PamHandle → IO Int
pamAcctMgmt : PamHandle → IO Int
pamChauthtok : PamHandle → IO Int               -- PAM_CHANGE_EXPIRED_AUTHTOK
pamSetcred : PamHandle → (establish : Bool) → IO Int
pamOpenSession pamCloseSession : PamHandle → IO Int
pamGetEnv : PamHandle → IO (List (String × String))
pamStrerror : PamHandle → Int → IO String
pamEnd : PamHandle → (status : Int) → IO Unit
pamAvailable : IO Bool
```

### `LeanSudo.Sys.Exec`
```lean
structure ExecSpec where
  path : String            -- absolute path passed to execve
  argv : Array String      -- including argv[0]
  env : Array String       -- "KEY=VALUE"
  uid : Nat
  gid : Nat
  groups : Array Nat       -- supplementary groups (setgroups)
  cwd : Option String      -- chdir after dropping privileges
  umask : Nat
  usePty : Bool            -- only honoured when a std fd is a tty
  background : Bool        -- `-b`
  closeFrom : Nat := 3
inductive ExitStatus where
  | exited (code : Nat) | signaled (sig : Nat)
/-- fork, drop privileges in the child in the order setgroups → setresgid → setresuid,
verify the drop with getres[ug]id (abort if it did not take), chdir, umask, close fds,
execve. The parent relays signals, waits, and returns the child's status. A failed
execve is reported back through a CLOEXEC pipe as an `IO.userError`. -/
runCommand : ExecSpec → IO ExitStatus
/-- exit(code) or re-raise the signal on ourselves with default disposition. -/
exitWith : ExitStatus → IO α
```

### `LeanSudo.Sys.Timestamp`
```lean
bootTimeNanos : IO Nat                -- CLOCK_BOOTTIME
getsid getppid : IO Nat
processStartTime : (pid : Nat) → IO (Option Nat)  -- /proc/<pid>/stat field 22
/-- open (O_NOFOLLOW, 0600, root-owned dir 0700 created if needed), lock,
pass contents to `f`, write back the result if `some`. -/
withTimestampFile : (uid : Nat) → (ByteArray → IO (Option ByteArray × α)) → IO α
removeTimestampFile : (uid : Nat) → IO Unit
```
Timestamp directory: `/run/lean-sudo/ts/<uid>`.

## Verified properties (targets)

1. **Default deny**: `evaluate [] s r = .deny`; no rule whose user list matches ⇒ deny.
2. **Soundness**: `evaluate s st r = .allow a` ⇒ there is a user-spec entry in `s` whose
   user, host, run-as and command lists all match `r` and which is the *last* such
   match, and it is not negated.
3. **Negation**: if the last matching command entry is negated ⇒ `.deny`.
4. **Authentication**: `a.needsAuth = false` ⇒ the deciding rule carries `NOPASSWD`
   or `authenticate` is off.
5. **Glob**: `fnmatch` agrees with literal equality on metacharacter-free patterns;
   `*` with `pathname` never crosses `/`.
6. **Environment** (sudo's env.c order): with `env_reset`, every output variable is
   set by sudo, whitelisted (`env_keep`, or `env_check` with a safe value) or comes
   from a trusted source (`env_file`, PAM); without `SETENV`, `LD_*` and `env_delete`
   entries never come from the caller, and the caller cannot override `secure_path`;
   `SUDO_USER/UID/GID/COMMAND` are correct unless an explicitly permitted later write
   sets them (as in sudo); no duplicate keys.
7. **CLI**: the command vector is exactly the operands after option parsing; `--`
   stops option processing; mutually exclusive modes are rejected.
8. **Timestamp**: a record is accepted only if same uid, same scope (tty/ppid/
   session identity incl. start time), age ≤ timeout and not in the future; `-k`
   invalidates every record of the current scope (sudo's `timestamp_remove`).
9. **Decision core**: `decide` yields `exec` only if the policy allows the request
   and either authentication succeeded, or no authentication is required (invoker is
   root, NOPASSWD/`!authenticate`, valid timestamp, or target = invoker without
   group change); the exec spec's uid/gid/groups equal the target's; its environment
   is `buildEnv`'s output.

## Fail-closed rules

* Unsupported sudoers constructs are parse errors (see `Ast.lean`).
* Every sudoers source must be a regular file owned by uid 0, not world-writable,
  and group-writable only when owned by gid 0. Included directories must be real
  directories with the same ownership/mode restrictions. Any violation ⇒ refuse
  to run, including in an included file/directory: skipping it could discard a
  denial and widen policy. Unlike sudo, insecure includes are fatal, not skipped.
* `requiretty`, PAM_TTY and log TTY use only a terminal whose device matches the
  process's controlling terminal, never an unrelated pty supplied on stdin.
* Timestamp-based authentication waivers are rechecked under the timestamp lock;
  invalidated or expired records require authentication, including with `-N`.
  Failed authentication never refreshes a record, and `-N` never writes one.
* PAM cleanup failures are warnings and preserve the command's exit status.
* Non-UTF-8 command-line arguments ⇒ refuse to run (Lean `String`s are UTF-8).
* Not running with euid 0 ⇒ the standard sudo "effective uid is not 0" error.

## Build

```
lake build LeanSudo Tests        # library, proofs, unit tests (Linux or macOS)
lake build sudo visudo           # executables (Linux only; on macOS: integration/build.sh)
lake env lean scripts/AxiomAudit.lean
integration/run.sh --build       # docker end-to-end suite (needs docker)
```
