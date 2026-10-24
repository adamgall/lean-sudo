# Handoff: status and context for the next session

Read this file first, then `DESIGN.md` (architecture, module contracts, list of
properties to verify), then the module headers. This file holds everything else:
what is done, what is left, the decisions made, and the lessons learned.

## Goal (from the user)

Rewrite `sudo` in Lean 4 as a **drop-in replacement on a Unix machine** (the target is
Linux, specifically Ubuntu 26.04 with glibc and Linux-PAM). Its security logic must
be **formally verified** in Lean, and it must be built and tested through to
completion. The repo is public at `github.com/adamgall/lean-sudo` and must be kept
pushed.

## Status at handoff

| Area | Files | State |
|---|---|---|
| Contracts | `LeanSudo/Sudoers/Ast.lean`, `LeanSudo/Policy/Types.lean` | frozen, done |
| Parser | `LeanSudo/Sudoers/Parser.lean`, `test/Tests/Parser.lean`, `test/fixtures/sudoers/*` | done, proved |
| Loader (includes, perms) | `LeanSudo/Sudoers/Load.lean` | done, builds; not yet exercised end-to-end |
| Glob + policy + defaults + `-l` listing | `LeanSudo/Util/Glob.lean`, `LeanSudo/Policy/{Eval,Defaults,List,Proofs}.lean`, `test/Tests/{Glob,Policy}.lean` | done, proved |
| Timestamp (pure + storage) | `LeanSudo/Timestamp.lean`, `LeanSudo/Sys/Timestamp.lean`, `c/ts.c`, `test/Tests/Timestamp.lean`, `test/Smoke/Ts.lean` | done, proved; root path untested |
| Sys core + PAM FFI | `LeanSudo/Sys/{Core,Pam}.lean`, `c/core.c`, `test/Smoke/Core.lean` | done, smoke-tested unprivileged |
| CLI + env + prompt | `LeanSudo/{Cli,CliProofs,Env,EnvProofs,Prompt}.lean`, `test/Tests/{Cli,Env}.lean` | done, proved (~195 `#guard` tests; help/usage text byte-identical to sudo 1.9) |
| Exec FFI (privilege drop, fork/exec, signals, pty) | `LeanSudo/Sys/Exec.lean`, `c/exec.c`, `test/Smoke/Exec.lean` | done: smoke 34/34 unprivileged, pty mode included; uid/gid changes as root not yet exercised |
| visudo | `Visudo.lean`, `LeanSudo/Visudo/{Core,Sys}.lean`, `c/visudo.c`, `test/Tests/Visudo.lean`, `integration/visudo-tests.sh` | done: 47/47 in docker as root (`integration/run.sh --visudo .lake/build/bin/visudo`) |
| Docker integration suite | `integration/` (`run.sh`, `tests.sh`, `ptyrun.py`, `Dockerfile`, `sudoers.d/`, `README.md`) | done: 78/78 pass against the reference sudo.ws 1.9.17p2 |
| **Decision core** | `LeanSudo/Core.lean` (+ proofs) | **NOT STARTED: next task** |
| **Main wiring** | `Main.lean` (currently a stub that exits 1) | **NOT STARTED** |
| sudoedit (`-e`) | `LeanSudo/Sudoedit.lean` | not started |
| Root import | `LeanSudo.lean` imports every finished module | done: `lake build LeanSudo Tests visudo` succeeds (48 jobs); the audit grep for sorry/axiom/native_decide is clean |
| Proof audit, README, install docs, LICENSE | — | not started (no LICENSE chosen yet: ask the user) |

### Slice notes worth knowing

* CliEnv departs from the original spec in the following ways (each checked against
  sudo's source):
  * `-i` together with `-E` is rejected.
  * `--preserve-env=a,b` behaves like `a=$a b=$b`, with the "not allowed to set the
    following environment variables: A, B" error.
  * Repeated `-u`/`-g`/`-p`/`-D`/`-C`/`-U` are usage errors.
  * `-l -u bob` with no command is a usage error.
  * `secure_path` and `SUDO_*` always win, even with SETENV (stricter than sudo).
  * `-i` sets PATH to the standard login PATH when there is no `secure_path` (sudo
    keeps the user's PATH: consider aligning).
  * `shell_noargs` is not honoured.
  * Extra `Options` field: `noUpdate` (`-N`).
  * `versionText` says `Sudo version 1.9.16 (lean-sudo 0.1.0)`.
  * `SUDO_HOME`/`SUDO_TTY` are not set.
* SysExec details: signals arriving from the command's own process group are forwarded
  for TERM/HUP/ALRM/USR1/USR2/PIPE, but not for INT/QUIT/TSTP. This is a deliberate
  difference from sudo. `-b` disables the pty. A monitor process handles the pty.
  `exitWith` clamps exit codes to 255.
* visudo details: an existing `<file>.tmp` means "busy". If visudo is killed at
  `What now?`, the stale `.tmp` has to be removed by hand; `visudo.ws` reuses it
  instead, which is worth adopting. Only the main file (or the `-f` file) is edited;
  includes are checked but not edited.

## Environment setup

### Linux (where development happened: Ubuntu 26.04 x86_64)
```
curl -sSf https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain none
export PATH=$HOME/.elan/bin:$PATH        # lean-toolchain pins leanprover/lean4:v4.35.0
lake build LeanSudo.Policy.Proofs        # build individual modules; see the per-area commands above
lake build Tests                         # compile-time unit tests (#guard)
integration/run.sh reference             # docker suite against sudo.ws (must stay 78/78)
integration/run.sh .lake/build/bin/sudo  # the same suite against our binary
```
* Core Lean only (no Mathlib or Batteries).
* `gpg` signing is configured globally on the original machine but fails without a
  tty, so commits there used `git commit --no-gpg-sign`.
* There was no root on the dev box. Everything that needs root is tested inside
  docker as real root, using setuid `/usr/bin/sudo` in the container.

### macOS
The pure Lean parts work natively on macOS: parser, policy, CLI, env, timestamp logic,
all proofs, and `lake build Tests`. **The C shim and the final binary are
Linux-specific** and will not build or run as a macOS sudo:
* `c/*.c` uses `setresuid`/`getresuid`, `CLOCK_BOOTTIME`, `/proc/<pid>/stat`,
  `close_range`, `pipe2` and Linux `getgrouplist`/termios details.
* PAM is `dlopen("libpam.so.0")` (Linux-PAM). macOS has OpenPAM
  (`/usr/lib/libpam.2.dylib`) with different conventions.
* Lean's bundled toolchain links against its own old-glibc sysroot on Linux. This is
  why PAM is loaded with dlopen at runtime instead of being linked.

**Recommended Mac workflow:**
1. Edit and prove natively, building pure modules such as `lake build LeanSudo.Core`.
   Avoid building `LeanSudo.Sys.*` and the exe on macOS.
2. Build the Linux binary inside a Linux container. First task on a Mac: add a builder
   stage, e.g. `integration/Dockerfile.build` (`FROM ubuntu:26.04`, install
   `curl git build-essential`, install elan, `COPY . /src`, `lake build sudo visudo`),
   and make `run.sh` accept `--build` to use the artifact. On Apple Silicon this
   produces an aarch64-linux binary. Lean supports linux-aarch64, and the docker
   suite runs in an arm64 Ubuntu container, so everything stays native arm64.
3. Run `integration/run.sh` exactly as on Linux (Docker Desktop or colima).

## Next steps (in order)

1. **On the Mac:** add the Linux builder container (see "macOS" above) and confirm
   `integration/run.sh reference` still passes 78/78 under Docker Desktop. On Apple
   Silicon the image is arm64 Ubuntu.
2. **`LeanSudo/Core.lean`: the pure decision core, plus proofs.** Design below. All
   of its inputs (Cli, Env, Policy, Timestamp) are finished.
3. **`Main.lean`: the IO shell.** Flow below. Add `LeanSudo.Core` to `LeanSudo.lean`.
4. Build `sudo` and run `integration/run.sh .lake/build/bin/sudo`. Iterate until
   78/78 pass. The suite is the behavioural spec; change tests only for genuine
   test bugs, and document why in `integration/README.md`.
5. Install `visudo` in the container and run `integration/visudo-tests.sh`.
6. sudoedit (`-e`/`sudoedit`). Optional but expected of a drop-in replacement. Model
   it on sudo's: copy files to temp files owned by the invoking user, read the
   originals as the target user, run the editor as the invoking user, write back as
   the target user, and refuse symlinks and files in user-writable directories.
7. Proof audit: `grep -rn "sorry\|admit\|axiom\|native_decide\|implemented_by" LeanSudo test`
   must print nothing (apart from comments). List every theorem in the README.
8. README: install instructions (setuid root, `/usr/bin/sudo`, `/etc/pam.d/sudo` and
   `sudo-i` already exist on Ubuntu), the supported-feature matrix, deviations, and the
   trust base (C shim, Lean compiler and runtime, libc, PAM).

## Decision-core design (planned, not yet written)

The guiding principle is that the IO shell gathers facts, the pure `decide`
returns a `Decision`, and the shell executes it. Every theorem is stated about
`decide`.

```lean
namespace LeanSudo.Core
structure Context where
  progname   : String
  opts       : Cli.Options
  invoking   : Principal          -- getuid + getpwuid + getgroups (the PROCESS groups, as sudo uses)
  host       : String             -- short hostname
  sudoers    : Sudoers            -- Load.load, entries mapped from Located; Policy.validate already passed
  settings   : Settings           -- resolveDefaults with runas + cmd (phase 2)
  target     : Principal          -- -u user / #uid; -g without -u ⇒ invoking user; else runas_default
  targetGroup : Option GroupInfo
  command    : Option Command     -- none = command not found (still needs auth first, see below)
  userEnv    : List (String × String)
  cwd        : String
  userUmask  : Nat
  ttyName    : Option String
  canon      : String → String    -- realpath oracle for literal sudoers command paths
  now        : Nat                -- bootTimeNanos
  tsScope    : Timestamp.Scope
  tsRecords  : List Timestamp.Record   -- Timestamp.load of the invoking uid's file ([] on any error)
inductive AuthReq | none | required (authUser : Principal)   -- invoking, or root (rootpw) / target (targetpw)
inductive Action
  | exec (plan : ExecPlan)        -- ExecSpec fields + envInput : EnvInput + pamService + login
  | print (stdout : String) (code : UInt32)      -- -l output, -l cmd
  | fail (msg : String) (log : Option String)    -- after auth: denial texts, command not found, -D refusal, -E refusal
  | validate | resetTimestamp | removeTimestamp
structure Decision where auth : AuthReq; action : Action; updateTimestamp : Bool
def decide : Context → Decision
```
Theorems to prove:
* `exec` implies `evaluate … = .allow a`.
* `plan.uid = target.uid`; gid and groups come from the target (or from `-g`).
* `auth = .none` with `exec` implies one of: the invoker is root, `¬a.needsAuth`, a
  valid timestamp (`Timestamp.lookup … = true`, and `-k` not given), or target equals
  the invoker with no group change.
* The plan's env is `buildEnv plan.envInput`, so the Env theorems apply.

The IO glue then does the following. If auth is required: check the timestamp again;
if it is invalid, run PAM authentication with up to `passwdTries` attempts, printing
`badpassMessage` between them. Then `pam_acct_mgmt` (always run, even for NOPASSWD),
`pamSetUser target`, `setcred`, `open_session`, `pamGetEnv`, then
`buildEnv {envInput with pamEnv}`, then `runCommand`, then `close_session` and
`pamEnd`, then `exitWith`.

Main IO flow:
1. Parse args. On error, print `Cli.formatError progname e` verbatim and exit 1.
2. `-h`/`-V`.
3. Check euid 0. sudo.ws's message is `<path> must be owned by uid 0 and have the
   setuid bit set`; the tests accept that or `effective uid is not 0`.
4. Reject non-UTF-8 args (fail-closed).
5. Load sudoers, warning with the `sudo: ` prefix.
6. `Policy.validate`.
7. Phase-1 defaults.
8. Resolve target user and group. An unknown user is reported as
   `sudo: unknown user X`, exit 1.
9. Resolve the command:
   * `-s` uses `$SHELL` or the invoker's shell; `-i` uses the target's shell with
     argv0 `-<basename>` and cwd set to the target's home.
   * Otherwise search PATH: `secure_path` if set, else the user's PATH; skip `.` and
     empty entries; the file must be regular and executable.
   * Exec the path as found (NOT the realpath), with argv0 as the user typed it.
     Multicall binaries dispatch on argv0.
10. Phase-2 defaults.
11. Read timestamp records.
12. `decide`.
13. Execute the decision.
14. Syslog (`authpriv`), for example `alice : TTY=pts/0 ; PWD=/home/alice ; USER=root ; COMMAND=/usr/bin/id`.
    A denial looks like `carol : command not allowed ; TTY=… ; COMMAND=…`.

## Reference behaviours learned (sudo.ws 1.9.17p2, verified in docker)

* On Ubuntu 26.04, `/usr/bin/sudo` is **sudo-rs**; the original is `/usr/bin/sudo.ws`.
  The suite uses sudo.ws as the reference.
* **sudo.ws asks for the password before refusing.** This covers "not in the
  sudoers file", "not allowed to execute", "command not found" and `-D` not
  permitted. With `-n` it prints `a password is required`.
* Messages:
  * `alice is not in the sudoers file.`
  * `Sorry, user carol is not allowed to execute '/usr/bin/cat /etc/shadow' as root on <host>.`
  * `Sorry, user bob may not run sudo on <host>.` (for `-l`)
  * `sudo: <cmd>: command not found`
  * `sudo: unknown user <u>`
  * `sudo: 3 incorrect password attempts`
  * `sudo: a password is required`
  * `sudo: a terminal is required to read the password; either use the -S option …`
  * `sudo: you are not permitted to use the -D option with <cmd>`
  * `sudo: sorry, you are not allowed to preserve the environment`
* Syntax errors: sudo.ws prints `file:line:col: syntax error` and **continues** with
  the parsable entries. **We deliberately refuse to run instead (fail-closed).** The
  test accepts both.
* Included files that are world-writable, owned by non-root, or group-writable with
  a non-root group are **skipped with a warning**: `X is world writable`,
  `X is owned by uid N, should be 0`, `X is owned by gid N, should be 0`. A
  world-writable `/etc/sudoers.d` is skipped entirely. A bad `/etc/sudoers` is
  fatal. `Load.lean` implements exactly this.
* A command matched by `ALL` implies SETENV, so alice may use `-E`. With `-E`, HOME
  stays the caller's.
* sudo.ws also sets `SUDO_HOME`, and `TERM=unknown` when TERM is unset. Neither is
  asserted by the suite.
* Without a tty, the timestamp is scoped to the parent process.
* `/usr/bin/id`, `cat`, `ls` and the other coreutils are **symlinks to one multicall
  binary** (rust coreutils in `/usr/lib/cargo/bin/coreutils/`). Two consequences:
  * Command matching requires equal basenames before comparing canonical paths.
    Policy does this, and the theorem `pathMatches_literal_basename` proves it.
  * Exec must use the path as found, with argv0 as typed.
* `-l <cmd>` for a disallowed command exits 1 with no output.
* glibc strips `LD_PRELOAD` from setuid processes anyway. The suite therefore also
  checks `LD_FOO`, `BASH_ENV`, `PYTHONPATH`, `PERL5OPT` and `BASH_FUNC_*%%`.

## Deliberate deviations and limitations (document in the README)

* Fail-closed parser: netgroups, IP/netmask hosts, digests, regex arguments, NOEXEC,
  INTERCEPT, CHROOT, TIMEOUT, NOTBEFORE/NOTAFTER, SELinux/AppArmor options and `CWD=~`
  are syntax errors. Options must come before tags. `Defaults!cmd` takes no
  arguments. `\xHH` escapes are not supported.
* Fail-closed Defaults: `noexec`, `intercept`, `env_file`, `restricted_env_file`,
  `runchroot`, `runcwd`, `closefrom_override`, `rlimit_*`, `log_subcmds` and more are
  errors (see `Policy/Defaults.lean`). Known-but-ignored names produce warnings: mail,
  lecture, insults, I/O logging, `exempt_group`, `fqdn`. Main should keep the
  `ignoring unsupported defaults entry` warnings quiet, because stock Ubuntu has
  `mail_badpass`.
* `!umask` is stored as `0o777`, meaning "do not change the umask". The exec plan must
  honour that.
* `-g` accepts only a group allowed by the run-as group list, or the target's primary
  gid. This is stricter than sudo for supplementary groups.
* Non-UTF-8 argv is refused. Non-UTF-8 environment entries are dropped.
* Timestamps are stored in `/run/lean-sudo/ts/<uid>`, not sudo's directory.
* `Policy.validate` MUST run before `evaluate`. Undefined aliases are treated as
  non-matching, which would make `!BADALIAS` a silent no-op.
* `sudo -A` (askpass), `-h host`, `-r`/`-t`, `-R`, `-T`: not supported.

## Slice APIs not shown in DESIGN.md

* Parser: `LeanSudo.Sudoers.parse (file text : String) : Except ParseError (List Located)`,
  where `ParseError.toString` gives `file:line:col: syntax error: msg`. Theorems:
  `parse_wellFormed`, `parse_line_pos`, `parse_file_eq`, `parse_command_absolute`.
  They are established by a final checking pass inside `parse`.
* Loader: `LeanSudo.Sudoers.load (warn : String → IO Unit) (host : String) (path := "/etc/sudoers") : IO (List Located)`.
* Policy (`namespace LeanSudo.Policy`):
  * `evaluate`
  * `validate`
  * `resolveDefaults s user host (runas : Option Principal) (cmd : Option Command) canon : Except String (Settings × List String)`, where the list holds warnings
  * `listPrivileges s st user host canon : String`
  * `notAllowedMessage user host`
  * Theorems in `Policy/Proofs.lean`: `evaluate_nil`, `evaluate_sound`,
    `evaluate_sound_run`, `evaluate_no_user_match`, `evaluate_append_negated`,
    `evaluate_append_deny_all`, `evaluate_noauth_run`, `evaluate_noauth_listing`,
    `evaluate_irrelevant`, `evaluate_congr`, `pathMatches_literal_basename`, and
    the Glob theorems (`fnmatch_literal`, `fnmatch_star`,
    `fnmatch_prefix_star_pathname`, `fnmatch_star_pathname`).
* Timestamp (`namespace LeanSudo.Timestamp`): `Scope`, `Record`, `scopeFor`, `valid`,
  `lookup`, `update`, `invalidate`, `encode`, `decode`, and `load` (decode or `[]`).
  Theorems: `decode_encode`, `valid_sound`, `lookup_iff`, `lookup_invalidate`,
  `lookup_update_self`, `lookup_update_other`, `lookup_timeout_zero`.
  `LeanSudo.Sys`: `ttyDevice`, `withTimestampFile`, `removeTimestampFile`,
  `bootTimeNanos`, `getsid`, `getppid`, `processStartTime`.
* Sys.Core additions: `umask (mask : UInt32) : IO UInt32`, which returns the previous
  mask.
* Pam additions:
  * `pamSetUser h user : IO Int`
  * `pamLastConvError h : IO (Option String)`, which returns the reason the
    conversation failed (`a password is required`, `a terminal is required …`,
    `timed out reading password`, `no password was provided`)
  * `ConvConfig` fields have defaults
* CLI (`namespace LeanSudo.Cli`): `Mode`, `PreserveEnv`, `Options`, `parseArgs`,
  `usageText`, `helpText`, `versionText`, `formatError progname e` (already includes
  the `sudo: ` prefix and usage), and `shellCommand`. `-i` together with `-E` is
  rejected, as in sudo.
* Env (`namespace LeanSudo`): `EnvInput` (with an extra `shellMode : Bool := false`),
  `buildEnv`, `envToArray`.
* Prompt: `LeanSudo.expandPrompt`.

## Process notes

The previous session ran parallel subagents, one per slice, each owning distinct
files, against the frozen contracts. Rules that worked:
* Build only your own modules. The box had about 3 GB of free RAM, and a bare
  `lake build` from several agents at once risks OOM.
* No `sorry`, `axiom`, `native_decide`, or `partial` on any function that has
  theorems about it.
* Unsupported constructs fail closed.
