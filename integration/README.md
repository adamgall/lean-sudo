# End-to-end sudo and visudo suites (Docker)

The sudo suite installs an implementation as the real setuid-root
`/usr/bin/sudo`, with `/usr/bin/sudoedit -> sudo`, in a throwaway Ubuntu 26.04
container. It exercises that binary as unprivileged users and root. The reference
is Ubuntu's sudo.ws 1.9.17p2 (`/usr/bin/sudo.ws`), not the distribution's default
`sudo` alternatives link. The separate visudo suite runs the selected visudo
against the same container fixtures.

Historical full-suite baseline (before replacing dependency mocks with real
services and removing cases without a real substitute):

| Suite | sudo.ws | lean-sudo |
|---|---:|---:|
| sudo | 918/918 | 918/918 |
| visudo | 154/154 | 154/154 |

These are shared compatibility suites, not a claim that every behavior is
identical: intentional safety differences are encoded in the expectations.
Ubuntu's sudo-rs remains an optional comparison target for the sudo suite; no
current pass count is claimed for it.

The only tests are these Docker end-to-end suites: no unit tests and no mocks.
Dependencies must be real software running in the container. Commands, editors
and execution-environment probes invoked by sudo are test inputs, not replacement
dependencies; use a real editor where the scenario is about interactive editing.
`/etc/hosts` and `/etc/netgroup` entries configure real NSS files backends.

The `background-syslog-exit` regression runs real rsyslog and compares traditional
`log_exit_status,syslog_pid` records with sudo.ws. The acceptance record identifies
the invoking sudo process; the EXIT record identifies the background supervisor.

## Running

```sh
integration/run.sh reference
integration/run.sh sudo-rs
integration/run.sh --build
integration/run.sh .lake/linux/sudo
integration/run.sh .lake/linux/sudo 'tty-|env-'
integration/run.sh reference '^sssd-'

integration/run.sh --visudo reference
integration/run.sh --visudo --build
integration/run.sh --visudo .lake/linux/visudo
integration/run.sh --visudo .lake/linux/visudo 'edit-'
```

The optional filter is an extended regular expression matched against test names,
not module filenames. `--visudo` does not accept `sudo-rs`.

Requirements: Docker and permission to use its daemon (Docker Desktop/Colima on
macOS, or a suitably configured Docker installation on Linux). Environment:

* `SUDO_IT_BASE`: suite base image; defaults to `ubuntu:26.04`, with a retry using
  `ubuntu:devel` if the default image build fails. An explicitly supplied base
  does not get that fallback.
* `SUDO_IT_IMAGE`: suite image tag prefix; defaults to `lean-sudo-it`;
  the runner appends `-amd64` or `-arm64`.

`integration/build.sh` builds Linux `sudo` and `visudo` from the working tree
using `integration/Dockerfile.build` and Docker's local artifact output, exporting
both to `.lake/linux-<arch>/`. Both build and run accept `--arch amd64|arm64`,
defaulting to the host architecture, and explicitly select Docker's Linux platform.
Native builds also copy both binaries into `.lake/linux/` for existing callers.
Build caches and image tags are architecture-specific. `--build` invokes the
builder before running the selected suite. The build script also accepts
`SUDO_IT_BASE` (default `ubuntu:26.04`, without the suite's fallback).
Its log is `integration/out/linux-build-<arch>.log`.

Output is TAP (`ok N - name` / `not ok N - name`), diagnostics and a summary.
The harness exits 0 when all selected tests pass, 1 for test failures, and 2
for a missing input binary or no matching tests; runner usage/image-build errors
also exit 2. Full transcripts and TAP copies are written to
`integration/out/<label>.log` and `.tap`; the suite image build log is
`integration/out/build-<arch>-<label>.log`. Standard labels are `reference`,
`sudo-rs`, `custom-sudo`, `visudo-reference` and `custom-visudo`, each suffixed
with the architecture. Other custom binary basenames affect the label.
`SUDO_IT_LABEL` overrides the full label and `SUDO_IT_OUT` overrides the output
directory (use an absolute path). Logs are assigned to the invoking host UID/GID.

## Architecture matrix

```sh
integration/build.sh --arch amd64
integration/run.sh --arch amd64 .lake/linux-amd64/sudo
integration/run.sh --arch arm64 --visudo reference
SUDO_MATRIX_JOBS=2 integration/matrix.sh
integration/matrix.sh --arch amd64
```

The matrix builds both architectures, then runs sudo and visudo for lean-sudo
and sudo.ws on each architecture: eight real Docker end-to-end runs. Parallelism
is bounded by `SUDO_MATRIX_JOBS` (1–8, default 2). `--arch amd64|arm64` builds
and runs only that architecture's four combinations. Docker must support the
selected Linux platforms; an ARM host normally emulates amd64.
Architecture-specific artifacts, cache IDs, image tags and run labels prevent
cross-architecture overwrites. The matrix saves transcripts, TAP and exit statuses
under `integration/out/matrix/`, then prints a compact eight-row summary.
It fails if any run fails, has missing/incomplete TAP, or the two implementations
have different pass counts for an architecture/suite pair. This checks the shared
suite's behavioral parity, not every possible input. Emulated amd64 results are
not native-kernel evidence: Rosetta does not faithfully support the ptrace,
strace and seccomp behavior exercised by these suites. Native CI is the authority
for architecture parity; emulated execution is unsupported for that evidence.

`.github/workflows/matrix.yml` runs the single-architecture matrix on native
`ubuntu-24.04` amd64 and `ubuntu-24.04-arm` arm64 GitHub runners, on pushes to
`master` and `ci/**`, or through `workflow_dispatch`. Both jobs upload
`integration/out/`, including their four-row summaries, even after failures.
The workflow caches Docker build layers per architecture. `SUDO_BUILD_CACHE`
selects a local Buildx cache import directory and exports the updated cache to
the same path with `-new` appended; the workflow rotates it after the run.
The architecture-specific Lake cache remains a BuildKit cache mount for warm
builds on a persistent builder.

Native CI run [40248622105](https://github.com/adamgall/lean-sudo/actions/runs/40248622105)
passed all eight combinations on the `ci/matrix` snapshot of product commit
`b1fc30a` plus the architecture harness. This is evidence for that snapshot,
not for subsequent uncommitted product changes. Its summary rows were:

```text
ARCH   SUITE   IMPLEMENTATION  PASS  FAIL  RESULT
amd64  sudo    lean-sudo       918     0  PASS
amd64  sudo    reference       918     0  PASS
amd64  visudo  lean-sudo       154     0  PASS
amd64  visudo  reference       154     0  PASS
arm64  sudo    lean-sudo       918     0  PASS
arm64  sudo    reference       918     0  PASS
arm64  visudo  lean-sudo       154     0  PASS
arm64  visudo  reference       154     0  PASS
```

No product architecture fix was required for that snapshot. The runner separates
semantic implementation labels from architecture-specific output labels:
reference-only expectations still receive `reference`, while transcript names
remain unique. Local Rosetta command timeouts did not reproduce on native amd64.

## Container and harness

`Dockerfile` installs sudo.ws, sudo-rs, Python, procps, util-linux, account/PAM
tools, `strace`, OpenLDAP (`slapd`, `ldap-utils`), SSSD and its LDAP/sudo/NSS
libraries. It also installs `locales`, `language-pack-de-base` and
`language-pack-fr-base`, and generates `de_DE.UTF-8` and `fr_FR.UTF-8`.
Translation tests assert actual German/French text as well as reference equality,
so missing catalogs cannot silently turn them into English-only comparisons.
`cracklib-runtime` supplies the dictionary that the stock `pam_pwquality` password
stack requires; without it every password change fails the dictionary check, so
expired-password changes could not succeed.

The image installs `sudoers.d/` fixtures as root:root 0440 alongside Ubuntu's
stock policy and validates them with `visudo.ws -c`. It copies `tests.sh`,
`ptyrun.py`, all `tests.d/` modules and the vendored `sudo-schema.ldif`.

`run.sh` builds the image and creates a container with
`--hostname sudo-it --network none --cap-add SYS_PTRACE --cap-add SYS_ADMIN`. Only
`integration/out/` is mounted, writable; host binaries and the visudo harness are
copied in. The container is removed on runner exit. `SYS_PTRACE` allows the audit
cases to use `strace` across credential transitions and inspect actual Linux
`USER_CMD` netlink records. `SYS_ADMIN` lets both sudo implementations install
their exec-interception seccomp filter without `no_new_privs`, which would change
set-ID command semantics. No host audit daemon or `AUDIT_CONTROL` capability is
required: strace observes real kernel audit traffic, not a replacement audit
service. Likewise, utmp readers and inotify are observation tools, not mocks.

Syslog tests run real rsyslog with imuxsock on `/dev/log`, disabled rate limiting,
a 256 KiB message limit and no control-character escaping. A shared harness
context preserves `%rawmsg%` bytes in JSON-framed output; a logger marker and
deadline-bounded polling drain the daemon before assertions. Mail tests invoke
Exim's sendmail interface and inspect local delivery in `/var/mail/root`, including
headers and the submitting identity in Exim's log; strace observes the real
sendmail arguments and supplementary groups. `example.test` is a local domain
and `admin` aliases to root; no external network is needed. Negative mail
assertions observe the real mailbox rather than a script standing in for an MTA.

Askpass scenarios run the packaged `ssh-askpass` GUI under Xvfb and type into it
with xdotool; `/proc` supplies the helper's real/effective/saved/filesystem UIDs.
SSH terminal-discovery tests use key-authenticated `ssh -T` sessions through a
real loopback sshd. PAM account and empty-password cases use pam_unix and actual
account state; the session-error case uses pam_limits against the kernel's file
descriptor ceiling. Non-generic challenges use pam_oath HOTP validation, including
rejection of an invalid token, rather than a permissive challenge module.
Shell-mode tests execute real Bash. All required packages are installed while
building the image, before the network-disabled tests start.

`tests.sh` is the root entrypoint. It installs the supplied sudo binary with mode
4755, creates the sudoedit symlink and adds a hostname entry if needed. Before
each selected test, `begin` restores `/etc/sudoers` and `/etc/sudoers.d` and clears
known sudo.ws/sudo-rs/lean-sudo timestamp and lecture state.

* `run USER SNIPPET` uses a clean environment, the user's home as cwd, stdin from
  `/dev/null`, and `setpriv --reuid --regid --init-groups` to run `/bin/sh -c`.
  `XENV` supplies extra environment entries.
* `pty USER SNIPPET ...` invokes `ptyrun.py` for terminal interaction; scenarios
  use `-e REGEX` to wait for output and `-s TEXT` to send input.
* Both helpers use a 40-second timeout with a further five-second kill grace.
  Individual fixtures may use shorter timeouts or their own subprocess handling.
* Assertions record failures until `end`, which emits the TAP result and failure
  diagnostics. Transcript logs include commands, status, stdout and stderr.

### Users and fixtures

All image-created test users have password `<name>pw` and a Bash login shell:

* `alice` belongs to `sudo` and gets the stock `%sudo ALL=(ALL:ALL) ALL` grant.
* `bob` has no stock sudo rights.
* `carol`, `dave`, `erin`, `frank`, `gina` and `henry` have the checked-in policy
  fixtures. They cover command/runas restrictions, aliases and negation, SETENV,
  argument matching, and sudoedit respectively.
* `ivan`, `judy`, `kate`, `liam`, `mona`, `nick`, `olga` and `pete` are spare users
  without checked-in grants. Modules install the policy needed for each case;
  these accounts are shared fixtures, not reserved to particular contributors.

Some scenarios create additional purpose-specific accounts or groups. The generic
reset only restores policy and timestamp/lecture state: tests changing passwords,
account metadata, PAM, NSS, `/etc/environment`, `/etc/hosts`, sockets or services
must restore that state themselves.

## Test layout and conventions

`tests.sh` contains the common harness and baseline scenarios: password input and
retry, noninteractive denial, runas users/groups, aliases and argument matching,
environment filtering, listing, tty prompts and timestamps, shell/login modes,
exit/signal status, policy-file integrity, setuid installation, sudoedit safety,
command-symlink races and controlling-terminal checks.

It then sources `integration/tests.d/*.sh` in filename order in the same shell.
There is no registration list or per-file ownership mechanism. Keep files named
for their area, use unique descriptive test names, and use the shared
`begin NAME && { ...; end; }`, `run`, `pty` and `expect_*` conventions. Install
per-test sudoers fragments inside the `begin` block; helpers needed by filtered
runs must be defined outside selected test bodies. Prefix module helpers and
scratch names to avoid collisions in the shared shell. Extend the relevant
area rather than creating contributor-owned files, and restore non-policy state
explicitly. The numbered prefixes control source order, not ownership.

| File in `tests.d/` | Names / areas covered |
|---|---|
| `10-parser.sh` | `parser-*`: extended grammar, escapes, include semantics, empty runas forms, command/argument regex token boundaries and invalid expressions. |
| `20-policy.sh` | `policy-*`: user/host/runas/group matching, negation, usrmerge and symlink paths, globs/regexes, digests, validity windows, list pseudo-command, netgroups and interface networks. |
| `30-defaults-list.sh` | `defaults-*`: exact short/long listing output, aliases/tags/quoting/digests/options, unknown-Defaults warnings and suppression, compiled environment defaults and scope/file order. |
| `40-cli-env-core.sh` | `cli-core-*`: help/version and option ordering, prompts, shell/login/edit modes, environment construction and PAM merging, preserve/assignment precedence, runas checks, listing/validation denial and cwd selection. |
| `50-shell-pam.sh` | `shell_*`: askpass/configuration, terminal discovery, logging/mail, lectures/insults/timeouts, PAM account/session behavior and expired-account cache protection. |
| `55-locale-time.sh` | `locale-time-*`: caller TZ isolation for validity windows, preserved command TZ, translated PAM/libc diagnostics, policy-locale regex matching and log timestamps/paths. |
| `56-nsswitch.sh` | `nsswitch-*`: source/action parsing and ordering, silent omission of unsupported backends, files fallback for empty selections, and no local-policy fallback when supported SSSD is unavailable. |
| `57-shell-residual.sh` | `shell-residual-*`: noninteractive authentication, visible passwords, EOF/interrupt accounting, file/syslog/audit events, real GID, dot/PATH lookup and timestamp scope/invalidation. |
| `58-command-lookup.sh` | `command-lookup-*`: runas-first lookup, invoker fallback, private directories, execute-bit/nonregular checks, list resolution and terminal dot-search results. |
| `58-sudoedit-parity.sh` | `sudoedit-parity-*`: temporary names/mtime, size/mtime copyback decisions, multi-file failures, editor selection/PATH/quoting/injection and diagnostic prefixes. |
| `59-shell-policy.sh` | `shell-policy-*`: unknown-identity error/event ordering, shell versus sudoedit authorization, non-generic PAM challenges and relative-command spelling/logging. |
| `60-exec.sh` | `exec-*`: resource limits, closed stdin, cwd failures, NOEXEC, timeouts/escalation, background/pty lifecycle, AppArmor, utmp, stay_setuid, signal relay and job control. |
| `61-timestamp-interop.sh` | `timestamp-interop-*`: bidirectional sudo.ws credential sharing, exact v2 layout, tty/ppid isolation, timeout and `-k`/`-K`, configured directory/owner, malformed/foreign records, first-slot validation, bounded dense/sparse scans and `-k command` avoiding all timestamp I/O. |
| `62-host-alert.sh` | `host-alert-*`: local-host DNS failures use raw startup syslog alerts, remote `-h` failures use stderr only, and early hostname callbacks precede configured logfile/JSON logging. |
| `63-local-bound-time.sh` | `local-bound-*`: system-zone America/New_York validity bounds, exact short/long UTC listings across winter/summer and historic DST gaps/folds, explicit-zone and caller-TZ isolation, and live NOTBEFORE/NOTAFTER allow/deny; restores `/etc/localtime` after every case and on exit. |
| `66-ext-auth.sh` | `ext-auth-*`: `-S` EOF newline after the prompt, bounded 1023-byte password reads (multi-attempt, split password, CR terminator), askpass exec-failure diagnostics, tty hangup/SIGHUP and SIGINT/QUIT/TERM during the prompt, a signal interrupting the read even when the password was buffered meanwhile (stopped reader), SIGTSTP at the `-S` and tty prompt (newline, stop or orphaned no-stop, time-stamp reopen for `-k`, fresh prompt, zero `timestamp_timeout` abandoning the password), `pam_group` groups from `pam_setcred` and the PAM session umask reaching the command. |
| `66-ext-core.sh` | `ext-core-*`: `-l`/`-ll`/`-U`/`-v` with no rules, typed command in list denials, PAM account checks for list and NOPASSWD paths, unset `PATH`, missing/non-executable `-s`/`-i` shell, `-V` with unwritable stdout, denied run-as-self and negated NOPASSWD rules without a prompt, sudoedit refusals without a PAM session, environment order, `-s`/`-i` argument unescaping, mail-only denials and relative sudoedit files from a deleted cwd. |
| `66-ext-edit.sh` | `ext-sudoedit-*`: missing files below writable ancestors, temporary files deleted/replaced/re-moded by the editor, fully random temporary names, environment-editor fallback and deleted-cwd relative-file diagnostics. |
| `66-ext-exec.sh` | `ext-exec-*`: SIGALRM/SIGCHLD to sudo with and without a tty or pty, monitor command line and process topology, command pty owner, foreign terminals inherited, forged helper markers, `-g` group among the supplementary groups and the digest command descriptor number. |
| `66-ext-logging.sh` | `ext-logging-*`: root-group logfile creation, JSON `runenv` order, `-s`/`-i` `COMMAND=` escaping, `TSID=` with I/O logging, `mail_always` exit mail and mail-only events, `-V` log file path. |
| `66-ext-parse.sh` | `ext-parse-*`: sudo.ws's first syntax diagnostic (token column, ordering), escaped command paths, quoted Defaults value column and colon-separated include search paths. |
| `66-ext-plugins.sh` | `ext-plugins-*`: built-in I/O logger loaded only as sudo.ws loads `sudoers_io` (policy-only `sudo.conf`, `sudoers_io` with options beside a log server). |
| `66-ext-robust.sh` | `ext-robust-*`: closed standard descriptors, `RLIMIT_AS` 1 GiB, small `RLIMIT_NOFILE`, deleted working directory (text and JSON logs) and signals pending before the prompt acting at exec. |
| `66-ext-sudoers.sh` | `ext-sudoers-*`: NUL bytes in names and lines, CWD value diagnostics, located Defaults warnings/errors and their order, missing main/included files, scoped Defaults order, `sudo.conf` NUL handling and timestamp alerts logged to syslog/mail. |
| `70-iolog.sh` | `iolog-*`: unmodified `sudoreplay.ws` interoperability, input/output streams, compression, permissions, error policy, path expansion, sequence wrap and password masking. |
| `80-i18n.sh` | `i18n-*`: byte-for-byte German/French/C diagnostics, help/listing/prompts, LANGUAGE precedence, missing-locale fallback and literal configured messages. |
| `85-jsonlog.sh` | `jsonlog-*`: json/json_compact/json_pretty file and syslog records for acceptance, denial, authentication rejection, exit/signal, runas group, repeated events and I/O-log linkage. |
| `95-coverage.sh` | `coverage-*`: differential CLI, authentication/listpw/verifypw, timestamps, umask, shell/cwd/environment, listing, sudoedit, signal and job-control matrices. |
| `96-sssd.sh` | `sssd-*`: real LDAP/SSSD roles, allow/deny/negation, runas, signed sudoOrder, global/role options, argument wildcards, short/long listings and NSS source/action ordering. |
| `97-group-plugin.sh` | `group-plugin-*`: shipped group_file/system_group providers, named/numeric membership, negation, aliases/runas/Defaults/listing, always_query_group_plugin and loader/init/ABI failures. |
| `98-logsrv.sh` | `logsrv-*`: real sudo_logsrvd TCP/TLS events and I/O, generated CA/client credentials, trust/identity failures, unreachable-server policies, failover, final commits, live disconnect/restart failure policy and serialized intercepted subcommands. |
| `99b-plugins.sh` | `plugin host`: shipped audit_json event structure/status and policy rejection, upstream sample I/O binary/terminal streams, loader diagnostics and upstream plugin version output. |
| `99c-fault-paths.sh` | `fault-*`: differential sudo.ws/implementation runs of failure and fallback paths: descriptor sweep, mailer and askpass with `close_range` unavailable, resource-limit warnings, expired-password change, `pwfeedback` erase/kill/EOF, audited intercepted and `log_subcmds` subcommands, unwritable audit log, declining I/O plugin, `sudoers_io` loaded with options beside a log server, sample approval rejection and intercepted-subcommand approval, log-server TLS initialization and name-resolution failures, unusable timestamp directories and records. |

The plugin build stage downloads sudo 1.9.17p2 and checks the SHA-256 published
on [sudo.ws](https://www.sudo.ws/releases/stable/) before building its unmodified
`sample_plugin.so` and `sample_approval.so`. Tests also use Ubuntu's shipped
`audit_json.so`, `sudoers.so`, `group_file.so` and `system_group.so`.
The sample approval plugin's business-hours policy reads the real clock in the
system time zone. `99c-fault-paths.sh` compiles a fixed-offset zone with the
system's `zic` and points `/etc/localtime` at it, restoring the original link
afterwards. Rejection uses a local 03:00 and is always reachable. The intercepted
subcommand case targets a weekday local 17:00:50, so the initial command and its
first subcommands are approved and a subcommand started after 17:01 is rejected.
glibc accepts offsets within one day, so between Saturday 17:00 and Sunday 17:00
UTC that case falls back to a weekday noon (all approved) or, when no weekday is
within reach, 03:00 (all rejected); the branch is recorded in the transcript and
both implementations always run under the same branch. Synthetic callback
failures, command-name approval rules and malformed log-server peers have no real
substitute and are not tested. No test-only plugin DSO is built or loaded.

### Fault-path fixtures

`99c-fault-paths.sh` runs each scenario first with `/usr/bin/sudo.ws`, then with
the installed implementation, restoring any mutated state before each run, and
requires identical exit status, stdout, stderr (with `sudo.ws` spelled `sudo`) and
observed side effects such as delivered mail, audit JSON or timestamp files.
Kernel-denied system calls use a classic-BPF seccomp filter that root installs
with `prctl` (allowed by `SYS_ADMIN`, without `no_new_privs`) before `setpriv`
drops to the invoking user; the filter is inherited by the setuid sudo and all of
its children. It makes `close_range` fail with `ENOSYS`, or makes setting one
resource limit (`prlimit64`/`setrlimit` with a new value) fail with `EPERM`,
while reads of the limit still work. The tool checks that the filter is in effect
before executing anything, so a kernel or emulator without seccomp support fails
the case instead of passing it vacuously. It knows the arm64 and amd64 system
call numbers only. Askpass under the descriptor filter uses a two-line askpass
program that prints the password: the scenario concerns the descriptor sweep
before `exec`, not the GUI dialog.

### Real remote logging fixtures

`98-logsrv.sh` starts the packaged `/usr/sbin/sudo_logsrvd` on loopback and writes
isolated event logs and I/O directories. TLS cases generate their own CA and
server/client keys with OpenSSL; no external network or trust-store modification
is required. Each daemon is stopped after its case. The same assertions run
against sudo.ws and lean-sudo, including the difference between audit-only and
I/O error policies and the audit-only client's lack of an exit record.

The fixture also saves `integration/out/<implementation>-logsrv-<case>.json`
snapshots. These preserve event metadata and exact stream bytes while removing
generated IDs, timestamps, peer addresses, and timing delays. Adjacent reads of
the same stream are coalesced, retaining their total byte counts: kernel read
chunk boundaries are nondeterministic. Reference and implementation daemon
output can then be compared directly.

The disconnect cases wait for the daemon to persist the command's first output,
terminate and restart the daemon while the command is still running, and verify
that neither implementation reconnects. The default policy stops the command;
`ignore_iolog_errors` lets it finish without further logging. Both retain the
same incomplete log. Additional `-result.json` snapshots record exact command
status, stdout and stderr.

### Real SSSD fixtures

`96-sssd.sh` starts its own services for each selected case; it does not use
systemd or an external LDAP server. It refuses to overwrite an already running
`slapd` or `sssd`. Each case saves the existing NSS/SSSD configuration and cache,
creates fresh LDAP data and isolated `cn=config`, then loads the vendored
`integration/sudo-schema.ldif` offline with `slapadd`. There is no schema download
at test time.

The fixture starts foreground `slapd` in a new session on
`ldap://127.0.0.1:1389/`, waits for an LDAP bind, and loads its user/group/sudoRole
entries with `ldapadd`. It configures SSSD's `nss` and `sudo` responders with LDAP
identity/sudo providers, and starts it using
`setsid setpriv --groups=sssd -- sssd -i --logger=stderr`. The supplementary group
preserves access to Ubuntu's package-owned private responder sockets.

A positive sudo.ws `/usr/bin/true` grant is the end-to-end readiness probe, even
for denial cases, so a dead responder cannot produce a false pass. Cases compare
the selected sudo's status and output with sudo.ws, including LDAP role names in
long listings. Cleanup stops the owned process groups, appends service logs to
the transcript, restores configuration/cache/policy and removes the case data;
an EXIT trap also covers interrupted setup. Loopback works with `--network none`.

## Compatibility and documented lean-sudo deviations

The remaining deviation list below mirrors the root [README](../README.md),
under **Fail-closed by design** and **Other differences from sudo.ws**:

* **A syntax error anywhere in the policy stops lean-sudo.** sudo.ws reports the error
  and carries on with the rules it could parse.
* **An insecure included file stops lean-sudo** (world- or group-writable, or not owned
  by root). sudo.ws skips the file with a warning.
* **Undefined aliases and alias cycles are errors** (sudo warns), because a
  `!UNDEFINED` that matches nothing would widen access.
* **An invalid `Defaults` value is an error** (e.g. `timestamp_timeout=abc`), because
  falling back to the default could widen access.
* Non-UTF-8 command-line arguments are refused; non-UTF-8 environment entries are
  dropped.
* A fractional `timestamp_timeout` is rounded down to whole seconds.
* Group-typed log-server frames fail with `unable to unpack ServerMessage size N`; sudo.ws may instead report `handle_server_message: unexpected type_case value 0`. Both refuse execution.

The integrity cases assert that insecure grants never take effect and check the
diagnostic; syntax-error cases allow either reference recovery or fail-closed
refusal. The group-writable include case specifically uses a non-root group.
NSS empty/unknown-source cases require the same silent files fallback from both
implementations. Visudo's alias cases encode its stricter validation rather
than skipping tests.

Unknown Defaults are not the same as invalid values: runtime
`defaults-unknown-warning` expects successful execution plus a warning, and
`ignore_unknown_defaults` suppresses it. Visudo checks reject unknown entries
and invalid values. There is no blanket expectation that an unsupported Defaults
setting makes runtime policy validation fail.

## Visudo suite

`run.sh --visudo` copies `visudo-tests.sh` and any custom visudo into the container
and overrides the entrypoint. If a custom visudo has a sibling file named `sudo`,
the runner also copies it to `/opt/impl/sudo` and sets
`VISUDO_SUDO_BINARY=/opt/impl/sudo`. The harness otherwise defaults to
`/usr/bin/sudo.ws`. The rejected-alias-edit regression makes that runtime
root-owned/setuid and checks it before and after editing, so a Linux build of
both executables tests the actual pair.

`visudo-tests.sh` restores policy before each case and invokes visudo directly,
normally as root, with `env -i` and a 40-second timeout. Scripted editors append,
leave unchanged, empty, fail, or wait for concurrent-lock tests; `What now?`
answers come from controlled stdin. Stock check output is derived from eligible
`/etc/sudoers.d` files (excluding names containing `.` or ending in `~`), retaining
an exact-output assertion as fixtures evolve. No implementation-specific tests
are skipped.

Coverage includes:

* Check mode, stdin, quiet/strict checking, explicit files, owner/mode flags,
  missing includes, syntax columns, invalid/unknown Defaults, duplicate and
  undefined/cyclic/unused aliases, and exact CLI help/version/error comparisons.
* Source-located Defaults callback warnings only for applied global/host/user
  settings, including `runchroot` deprecation, `SUDO_USER` selection, quiet mode,
  and parser-before-callback diagnostic ordering. Edit mode emits those warnings
  before the editor and again when checking the edited policy; unused-alias
  warnings remain in the final semantic-check phase.
* Valid edits, discard on `x`/EOF, re-editing, the explicit dangerous `Q` override,
  unchanged/empty files, editor precedence/arguments/status, new files and
  ownership/mode preservation or correction.
* Explicit `@include`/`#include` editor order, whole-session discard, includes
  added during editing, empty includes, and includedir entries checked without
  ordinary editing. `-I` suppresses the initial include-editor pass, not parsing;
  newly discovered includes and error-driven re-editing still get exercised.
* Concurrent record-lock exclusion, interoperability with visudo.ws in both
  directions, busy explicit includes, stale temporary-copy reuse, signal cleanup,
  unchanged symlinked includes and continued installation after a per-file error
  (with the failed temporary copy retained).
* Edit-mode `-f -` as a literal filename, versus check-mode stdin. Export
  compatibility (`-x`/`--export`) is compared both with Ubuntu's missing
  `cvtsudoers` PATH name and with `cvtsudoers.ws` exposed under that name; successful
  JSON output is compared byte-for-byte.

Temporary-copy timestamps are applied with `futimens` before the write descriptor
is closed, rather than resolving the temporary pathname again. Export command
lookup stays compatible with the reference's configured `PATH` (including the
system default when unset), but Lean constructs absolute candidate paths and
calls `execve` explicitly. A root-configured `PATH` therefore remains trusted;
this does not pin export to Ubuntu's `cvtsudoers.ws`. Unlike the reference,
lean-sudo inserts `--` before the input filename so a leading dash cannot become
a converter option.

Lean-sudo's visudo rejects undefined/cyclic aliases even without `-s`, including
invalid unused definitions, to avoid installing policy its runtime would refuse.
Reference comparisons use strict mode where appropriate; unused-invalid-alias
cases assert the intentional difference explicitly. Rejected edits retain the
existing policy on `x`/EOF, while the deliberately dangerous `Q` override remains
available.

## Randomized conformance comparison

```sh
integration/conformance.sh --seed 2119172 --sudo-cases 3000 --visudo-cases 3000 \
  --budget 6000
```

This runs both implementations in one disposable integration-image container,
using `.lake/linux/sudo` and `.lake/linux/visudo`. Build those first with
`integration/build.sh`. `CONFORMANCE_SUDO` and `CONFORMANCE_VISUDO` override the
input binaries; `CONFORMANCE_IMAGE` selects an existing integration image;
`CONFORMANCE_OUT` changes the host output root. The default image is
`lean-sudo-it-<native architecture>` and is built if absent. The container uses
the same network isolation and capabilities as `run.sh`, plus `--init` so that
orphaned mailer and command processes are reaped and stray-process detection
sees only live processes.

`integration/conformance/generate.py` implements a seeded policy grammar:
user/runas/host/command aliases, negation, command tags, CWD/CHROOT/TIMEOUT and
validity bounds, all five Defaults bindings, environment/authentication/logging/
mail/resource-limit options, SHA-224/256/384/512 digests, glob and regex command
matching, includes and include directories, malformed syntax and alias/default
errors. Invocation families exercise listing, validation, invalidation, user and
group selection, shells/login shells, environment preservation and assignments,
working directory, descriptor closure, hostname, help/version, sudoedit,
unusual argument bytes (including control bytes and one invalid UTF-8 byte),
`VAR=value`, correct/incorrect stdin passwords, and terminals.
Visudo receives both grammar-generated and single-character-mutated policies
with `-c` or `-c -f /etc/sudoers`.

About half of the sudo scenarios also carry a seeded process-state dimension,
applied identically to both sides by `conformance/launch.py` before it drops to
the invoking user and `execve`s sudo with a raw environment block: inherited
extra descriptors (3, 4, 9, 63, 64, 255, 1000, 4095; some close-on-exec),
closed stdin/stdout/stderr, `RLIMIT_NOFILE`/`NPROC`/`CORE`/`FSIZE`/`STACK`/`AS`,
umask, a deleted or mode-000 working directory, a 100 KB entry, 1500 entries,
invalid UTF-8, an entry without `=`, an empty name and duplicates, and
SIGINT/SIGTSTP+SIGCONT/SIGTERM/SIGHUP/SIGPIPE/SIGQUIT/SIGUSR1 delivered to the
front-end sudo at seeded delays while it prompts (stdin withheld; delays from
launch) or while the recorder sleeps (delays from the moment the recorder has
written its observation). The runner waits (up to 250 ms) until each signal is no
longer pending in the target before sending the next, so a following SIGCONT
cannot discard a stop signal that was not yet delivered, and withheld stdin is
released 100 ms after the last signal, so the password never races the delivery;
either race made sudo.ws itself nondeterministic. Terminal scenarios run `stty -a`
after sudo exits, so terminal mode restoration is part of the compared transcript.

Both sides run through the same canonical executable path and clean initial
policy/timestamp/edit/log/mail state. PAM is real `pam_unix` with `nodelay` to
avoid spending the campaign budget on authentication-failure delays. Real
rsyslog captures raw records and uses logger barriers; Exim delivers local mail.
Comparison retains exit status, stdout, stderr, logfile, syslog/JSON bytes,
mailbox, sudoedit content and the recorder's real/effective/saved IDs,
supplementary groups, cwd, umask, environment (as a mapping and as the raw
ordered `/proc/self/environ`), open descriptors/flags, resource limits, signal
mask and argv. It also compares the files created, deleted and modified (type,
mode, owner, size, mtime) under `/run/sudo`, `/var/log`, `/var/lib/sudo`, `/tmp`
and the test users' homes; anything created there is removed before the next
side runs. After each side the runner waits for sudo/sendmail/Exim to finish,
flushes and empties the Exim queue, and records and kills any other process
left behind. The Python recorder writes a pre-created,
root-owned, mode-0666 file in a root-owned directory so non-root runas scenarios
can report too; this is an observation fixture, not a privilege boundary.

Independent of equality, three invariants are checked on lean-sudo: it is not
terminated by SIGSEGV/SIGBUS/SIGABRT/SIGILL/SIGFPE/SIGSYS/SIGTRAP, it does not
time out where sudo.ws finished, and it leaves no stray process.

Normalization is limited to timestamp encodings, process IDs, generated mail/
JSON identities, pipe/socket inode numbers, terminal allocation numbers and
sudoedit temporary suffixes. No diagnostic wording, whitespace or status is
rewritten. Terminal execution uses `ptyrun.py`; stdout and stderr on that
terminal necessarily form one transcript, while non-terminal channels remain
separate. JSON logs remain text so duplicate keys and malformed reference output
are not silently lost.

Only five explicit deviation rules filter findings, all decided on observed
evidence rather than on what the generator intended. All but the last also
require that lean-sudo rejected (nonzero status, no recorder output):
`fail-closed-policy-syntax` (sudo) requires a syntax diagnostic from both sides;
`fail-closed-alias-resolution` requires lean-sudo's `..._Alias "X" referenced
but not defined` or `cycle in ..._Alias` diagnostic, no syntax error from
sudo.ws, and (visudo) sudo.ws accepting the file, or else that the two
observations are identical once exactly those `file:line:col:` alias
diagnostic lines are removed from lean-sudo's stderr;
`fail-closed-default-value` (sudo) requires an `is invalid for option`
diagnostic from both sides;
`non-utf8-arguments-refused` (sudo) requires an invalid UTF-8 argument and a
lean-sudo diagnostic with no log record;
`non-utf8-environment-dropped` requires a generated invalid UTF-8 environment
entry and that lean-sudo's whole observation equals sudo.ws's once exactly the
invalid entries are removed from the recorder's environment and from sudo.ws's
JSON `submitenv` arrays (where sudo.ws logs them with `\xNN` escapes). These correspond to
the root README's **Fail-closed by design** list. The remaining documented
differences are not exercised specially and receive no blanket exemption.
When a scenario closes stderr and lean-sudo rejects (nonzero status, no recorder
output), its diagnostic cannot be observed, so the runner repeats the scenario
once with the standard descriptors open; only if that companion run matches
one of the rules above is the original counted as that deviation. One complete
example of each observed
named deviation is retained.

Findings go to `integration/out/conformance/seed-<seed>/`: `findings.jsonl`
retains every unfiltered failing scenario and raw observations; `summary.json`
and `summary.txt` report counts. A scenario can belong to several difference
classes: environment ordering (`record.environ(order)`), each created-file
prefix (`files.created[...]`), other file changes, each invariant together
with lean-sudo's first output line, and otherwise mode, grammar family and the
set of differing observable paths. Each class has `case.json`, `sudoers` and
`difference.diff`. Shrinking first resets each process-state dimension, then
delta-debugs sudoers lines and (sudo mode) argv chunks while the class still
occurs; `--shrink-budget` bounds comparison attempts per class (default 24).
The time budget covers generation, comparison and shrinking; budget exhaustion
or unshrunk classes is a failure, not a clean result. `--timeout` bounds each
invocation (default five seconds).

Replay a saved reproduction inside the same image:

```sh
integration/conformance.sh --replay /out/conformance/seed-2119172/CLASS/case.json
```

The runner exits nonzero on any unfiltered difference. Its generated
classification is a provisional parity-bug classification, not proof of cause;
inspect the retained raw observations and reduced input to distinguish a
product bug, reference quirk, or harness defect. The recorder observes a Python
process after interpreter startup, not every pre-exec kernel detail. Delivery
and terminal observation are bounded, not proofs of absence of late events.
This is randomized end-to-end conformance testing, not a correctness proof or
an exhaustive policy/argument search.

### Campaign result (seed 2119172)

Product: main tree at commit b1fc30a plus working-tree edits, Docker build of
2026-10-25 18:46 (arm64).

```
SUMMARY seed=2119172 sudo=3000 visudo=3000 equal=3065 deviations=457 differences=2478 classes=129 shrunk=129 unshrunk=0 budget_exhausted=false
```

Filtered deviations: `fail-closed-alias-resolution` 219, `fail-closed-default-value`
116, `fail-closed-policy-syntax` 109, `non-utf8-arguments-refused` 13. The 129
classes reduce to these root causes, all classified as lean-sudo parity bugs
(sudo.ws is the reference) unless stated; ids are directories under
`integration/out/conformance/seed-2119172/`:

* `8de19657fe2f` the `logfile` is created group-owned by the invoking user's
  gid (`0:1009`) instead of `0:0`.
* `443d51c1ea6c`, `d19fc07e9663` command environment order differs (`MAIL` and
  `SUDO_HOME` placed differently), also visible in JSON `runenv`.
* `ab69ed831c70` crash: `RLIMIT_AS` 1 GiB aborts with "failed to create thread"
  (SIGABRT) where sudo.ws runs normally.
* `824622ab9b1e`, `74b818c43d44` and 3 more crash classes: two closed standard
  descriptors abort (libuv `uv__close` assertion); 39 further classes (e.g.
  `cad3e82f0994`, `0e4eae29cb7d`): a single closed std descriptor is not
  reopened on `/dev/null` as sudo.ws does, so the command sees it closed.
* 27 classes (e.g. `79550e0d9296`, `a35ccc529271`): a deleted working
  directory makes lean-sudo fail "No such file or directory"; sudo.ws runs,
  lists, or reports usage.
* 14 classes (e.g. `e7bbf3048a23`): `RLIMIT_NOFILE` 24 or 64 makes lean-sudo
  fail "Invalid argument" (sudoedit: "command not found").
* `d5ca240b31f2` sudoedit refusing a writable directory still opens and closes
  a PAM session.
* `c2f42e1a997f`, `580002c49793`, `386e36ca4dee`, `e0ecbb80bf7a` with `-g`
  the run-as group is missing from supplementary groups, and the PAM-session
  umask (`pam_umask`, 002 for a user-private group) is not applied.
* `9aff8e1c1b8f`, `03f89ec0a825`, `77962f74ddf7`, `43dfe895e170` digest
  commands are executed from a different descriptor number (`/dev/fd/10` vs
  `/dev/fd/6`).
* `10780626c6aa` `-s`/`-i` log `COMMAND=` without sudo.ws's backslash escaping
  of the shell `-c` argument.
* `bde0dbfea7b3` `-l -U other` for a user with no rules exits 1 with stderr and
  logs "command not allowed"; sudo.ws prints to stdout and exits 0.
* `cb2568842da5`, `6c1f42476def` `NOPASSWD: ALL, !cmd` with `-n`: lean-sudo
  asks for a password instead of reporting "not allowed".
* `26671526285c`, `e3433f895fee` `LOG_OUTPUT`/`log_input` log lines lack `TSID=`.
* `9f9f7cb7e67e` with `mail_always` the exit-status record (`EXIT=0`) is neither
  logged nor mailed.
* `68b439731a63` SIGINT while prompting on a pipe kills lean-sudo (status -2);
  sudo.ws treats it as a failed attempt.
* `2e603cd08fa6` `-V` as root omits "Path to log file:".
* 21 visudo classes (e.g. `d0d6ba5a642d`, `b521c64620f9`): the `^~~~` underline
  length differs and lean-sudo stops after the first syntax error where
  visudo.ws reports every one; `eed3146b26e4` wrong column for a bad `logfile`;
  `5bba0d1306f7` include path containing `:` reported whole;
  `a785bc4b8d85`, `138797fa509f` lean visudo accepts a `Cmnd_Alias`/`Defaults!`
  command with a backslash-escaped path that visudo.ws rejects.

Harness issues found and fixed during the campaign: binaries copied by
`docker cp` kept the host uid (now chowned to root), unreaped zombies (now
`--init`), late reference mail leaking into the next run (now drained per
side), and unnormalised Exim 4.99 message ids and `unix_chkpwd[pid]`.

## Comment-free source policy

Run `scripts/check-no-comments.sh` from any directory to check tracked Lean, C,
Python, shell, Dockerfile and ignore files. It reports `file:line: comment` and
exits 1 on violations. The checker also scans recognized Python, Perl, C and
shell heredocs. Shebangs and Docker's syntax parser directive remain executable
metadata. Sudoers fixtures, sudoers heredocs, LDIF, Markdown and license files
are data, not source comments; their parser-test content must remain intact.
The checker uses only Bash, Git and Python's standard library.

### Harness invariants

The reference contract is Ubuntu's sudo.ws 1.9.17p2. Differential tests retain
the same `argv[0]` and compare complete output, including whitespace and final
newlines, rather than rewriting diagnostics. Authentication may precede a
policy denial, so tests that target denial either supply the password or accept
the reference's authentication-required disposition.

The isolated container has no external network or eligible non-loopback
interface. The harness maps its hostname locally to avoid unrelated resolver
warnings. State is restored before each case and log ownership is handed to
the host immediately, including for aborted runs. `run` uses a clean environment,
the user's home directory and no terminal; `XENV` supplies the next invocation's
extra environment. `pty` uses a fresh controlling terminal. `ptyrun.py` waits
for each expectation only after the preceding match and accepts terminal control
bytes through `-s`.

### Regression fixture design

* Timestamp interoperability uses genuinely authenticated reference tickets,
  explicit little-endian 64-bit records, stable parent processes and private
  sessions/directories. Never pipe authentication into a shell function or use
  a host user's timestamp directory. Global slot identity ignores start time,
  but timestamp validity checks both timespecs. Unsupported records retain
  their declared sizes and original bytes. Sparse/dense fixtures exercise
  traversal, not an artificial size cap. Lock tests modify only the locked
  record and restore authenticated bytes before unlocking; inotify separately
  detects forbidden access. A four-second sleep exceeds the configured
  0.05-minute timeout.
* System-local validity bounds use libc `mktime(tm_isdst=-1)`, not today's UTC
  offset. Historical root listings test winter, summer, spring gaps and autumn
  folds without changing the clock; a fresh process resolves ambiguous folds.
  Timezone restoration preserves symlinks and metadata without following the
  replacement destination. Live denial tests include an always-valid command
  as a readiness control.
* Locale tests prove translations are actually installed before comparing
  diagnostics. Generic PAM prompts, explicit literal prompts, libc strerror
  and gettext domains are distinct contracts. Regex `.` in the C locale matches
  a byte, not a multibyte character. Caller TZ must not change policy time
  evaluation, but an allowed TZ remains available to the executed command.
* Command lookup searches as runas before retrying as the invoker. A regular
  file needs any execute bit; successful lookup does not grant directory access
  at execution. A dot-only result is terminal rather than a reason to retry
  under different credentials. Editor lookup sees secure_path before env swap.
* Jails are self-contained rather than relying on merged-/usr host symlinks;
  policy and identity come from host NSS. The jailed editor intentionally cannot
  open the host temporary pathname. Absolute symlink escapes, missing NOEXEC
  libraries and retained command roots follow the documented fail-closed
  deviations. A literal directory named `*` must not reinterpret CHROOT=*.
* Intercept terminal tests keep commands in sudo's foreground process group;
  an interactive job-control shell would invalidate that fixture. Background
  execution is observed before the parent exits. CLONE_FS tests synchronize a
  real interpreter's cwd change after authorization, rather than racing it.
  Cleanup includes stranded commands and brokers.
* Logging comparisons retain priorities, event fields, duplicate JSON keys,
  spacing and record counts. Only transport times, process identities and
  generated identities are normalized, with identity correspondence checked
  first. No-mail assertions cover a bounded delivery interval. Event-only
  log-server clients do not wait for commit acknowledgements, and the
  reference audit-only client closes without an ExitMessage.
* Upstream audit_json preserves repeated event keys but ships malformed named
  array values and a 10-4-4-4-10 UUID grouping. Its narrowly scoped normalization
  preserves every event pair. Approval-plugin wall-clock policy is exercised
  only through version queries. Group-plugin ABI corruption locates the actual
  exported field through the loader mapping.
* SSSD cases own fresh LDAP data, caches and foreground service groups. A real
  positive command proves readiness even for negative cases. Preserve packaged
  ownership and the supplementary sssd group; never stop unrelated daemons.
  LDAP insertion order must not substitute for signed sudoOrder. NSS SUCCESS
  includes DENY, and unavailable SSSD must not silently grant access via files.
* GUI askpass runs on a real X server and waits for the visible window. HOTP
  tests use consecutive real counters, then prove that invalid tokens fail.
  PAM's hard-limit test exceeds the kernel ceiling rather than mocking failure.
  Terminal replay uses the packaged, unmodified sudoreplay.

The test-image build context is `integration/`; the Linux builder uses the
repository root. Apple Silicon builds matching aarch64-linux binaries. The
toolchain layer changes with `lean-toolchain`, and `.lake` is a locked cache
mount. The upstream archive checksum is published at
<https://www.sudo.ws/releases/stable/>. The offline MTA delivers root and
admin@example.test mail into the real root mailbox.

`scripts/loc.sh` counts all tracked implementation lines, including blank lines,
under LeanSudo and c plus the executable entrypoints. Harness, tests and docs
are excluded. Non-whitespace bytes and lines over 100 columns are also reported
so joining lines cannot masquerade as a size reduction.

## Independent sudo-rs compliance suite

```sh
integration/external/run.sh
integration/external/run.sh .lake/linux-arm64
```

The first command uses the existing `.lake/linux/{sudo,visudo}` artifacts;
build these with `integration/build.sh` first if absent. Docker must support
the artifacts' architecture. The runner requires access to the Docker daemon
socket, including permission to create and remove containers. This socket gives
the controller host-level Docker authority; use a disposable development daemon,
not a production daemon.

The suite is the independently written
[sudo-rs compliance suite](https://github.com/trifectatechfoundation/sudo-rs),
in `test-framework/sudo-compliance-tests`, pinned to commit
`5edfc693694224d43166821fdd112411a4c1b2bd`.
The build downloads its source archive and verifies SHA-256
`369ac95040d5d84f69494e28527f11634913f2f9bac03ab0877ce1c371466aa6`;
third-party source is kept inside the runner image, not vendored here. Cargo
uses the upstream lockfile. Test assertions and Rust framework code are unchanged.
The only upstream-file replacement is the original-sudo fixture Dockerfile,
which selects one of our two locally built fixture images.

Both fixture images use Ubuntu 26.04 and the upstream Linux fixture dependencies
and setup. The reference explicitly installs `/usr/bin/sudo.ws` as root-owned
setuid `/usr/bin/sudo`, rather than using Ubuntu's sudo-rs alternative, and
installs `visudo.ws` as `visudo`. The other fixture substitutes the supplied
lean-sudo and visudo binaries with the same ownership and permissions. Both
provide `sudoedit -> sudo`. The suite's real per-test Docker containers retain
upstream's `--net=none` and default capabilities; this harness adds no privilege
or security-option exceptions.

Both runs use `SUDO_UNDER_TEST=theirs`, so original-sudo expectations and version
branches apply equally to both implementations. All upstream ignored tests are
included. This is not sudo-rs's narrower CI gate. The complete compliance package
also contains system `su` checks: `su` is unchanged in both images, so those are
not evidence about a lean-sudo implementation of `su`. Optional upstream
AppArmor-feature tests are not enabled. Upstream version-dependent early returns
remain intact, so an `ok` outcome need not exercise every branch. Upstream
omissions and limitations remain; passing this suite is not a proof of complete
sudo compatibility or security.

The controller enumerates the compiled upstream test inventory, then runs every
test in a separate process with `--exact --include-ignored --nocapture`. This
retains diagnostics even when a test hangs, and bounds each test independently
without omitting the rest of the suite. A timeout is an explicit `TIMEOUT`
outcome, not a pass. A Docker CLI shim only adds `--cidfile` to real container
creation calls. Upstream removes normal test containers; on abnormal termination
the controller removes exactly the recorded containers. No test assertion or
dependency is mocked.

Results are written under `integration/out/external/`:

* `reference.log` and `lean.log`: concatenated verbatim test stdout and stderr.
  `reference.cases/` and `lean.cases/` retain each individual verbatim log.
* `*.inventory.txt` and `*.results.json`: full test inventory, per-test exit
  codes, elapsed times, explicit timeout outcomes and raw-log paths. The `.exit`
  files record controller status (0 clean, 1 failures/timeouts, 2 infrastructure).
* `reference.tsv` and `lean.tsv`: sorted per-test outcomes.
* `outcomes.diff.tsv`: every changed per-test outcome.
* `findings.txt` and `report.json`: tests passing on sudo.ws but failing on
  lean-sudo (including timeouts), with upstream assertion diagnostics. The JSON
  separately records reference failures/timeouts, which are excluded from
  lean-sudo findings even when both implementations fail.
* `*.pin`, `*.image.json`, and `*.version.txt`: source pin, actual fixture image
  identities, package version, binary checksums and full `sudo -V` output.
  Image-build logs are retained separately.

The command exits 1 for differential findings, 2 for incomplete results or
infrastructure errors, and 0 when every reference-passing test also passes on
lean-sudo. Failed or missing test summaries cannot become a successful comparison.
No allowlist suppresses implementation differences, including deliberate ones;
classify reported findings against the project's documented deviations.

Environment controls are `SUDO_EXTERNAL_OUT` (output directory),
`SUDO_EXTERNAL_THREADS` (concurrent test processes, default 4),
`SUDO_EXTERNAL_TIMEOUT` (per-test timeout in seconds, default 120),
and `SUDO_EXTERNAL_SOCKET` (daemon socket, default
`/var/run/docker.sock`). Runs in this checkout are serialized with
`integration/out/external.lock`. The upstream framework uses the shared
`sudo-test-og` image tag; do not run another copy of that framework concurrently
against the same daemon. Images remain available for inspection after the run.

### Recorded independent-suite result

The completed arm64 run is in `integration/out/external-final/`, produced with:

```sh
SUDO_EXTERNAL_OUT="$PWD/integration/out/external-final" integration/external/run.sh
```

| Implementation | Passed | Failed | Timed out | Total |
|---|---:|---:|---:|---:|
| Ubuntu sudo.ws 1.9.17p2-1ubuntu3.2 | 851 | 10 | 0 | 861 |
| lean-sudo | 311 | 546 | 4 | 861 |

The command exited 1. There are **540 reference-pass / lean-fail findings**:
536 assertion failures and four timeouts. The ten reference failures are excluded.
The complete test-name list and every corresponding assertion diagnostic are in
`external-final/findings.txt` and `external-final/report.json`; both verbatim
aggregate logs and all 1,722 individual test logs are retained there.

This run identifies its lean binaries by SHA-256, not the changing working tree:

* sudo: `a0c510bd1ab94989460aac5f3deaee6c99cf82e82ae681b2e8b0b32258e7add5`
* visudo: `5c15277b1ecda62afa3d024d77507d26f1b6de2b501f77a2c088c46536e15fb0`

454 findings contain `sudo: unable to determine timestamp process identity`.
One small upstream reproduction is
`sudo::sudoers::user_list::user_name`: policy
`root ALL=(ALL:ALL) NOPASSWD: ALL`, followed by a direct root
`docker exec <fixture-container> sudo true`, without a wrapping shell. The
reference test passes; lean-sudo exits 1 with that diagnostic. This is a
provisional parity-bug classification, not 454 independently established bugs.
The report does not suppress failures caused by this common prerequisite.

The four 120-second timeout findings are:

* `sudo::use_pty::allocates_a_second_pty_which_is_assigned_to_the_command_process`
* `sudo::use_pty::process_state`
* `sudo::use_pty::spawns_three_processes`
* `sudoedit::temporary_file_is_deleted_when_terminated_by_signal`

Separate visudo findings include updating an unprivileged user's existing file
(`unable to set (uid, gid) ... Operation not permitted`), the undefined-alias and
alias-cycle `What now?` interaction, and failure to fall back from a nonexecutable
environment-selected editor. The alias cases may overlap the documented
fail-closed policy; other failures also require classification rather than
assuming every differing assertion is a security defect. No product code was
changed to obtain these results.

### Timestamp-identity fix rerun

After the integrator's timestamp-identity fallback change, the main tree was
rebuilt with `integration/build.sh --arch arm64`. Only lean-sudo was rerun:

```sh
SUDO_EXTERNAL_OUT="$PWD/integration/out/external-postfix" \
  integration/external/run.sh --lean-only .lake/linux-arm64
```

`--lean-only` requires completed `reference.*` results and `reference.cases/`
in the selected output directory. This run copied those unchanged from
`external-final/`; it did not rerun sudo.ws. Original evidence remains intact.

| Implementation | Passed | Failed | Timed out | Total |
|---|---:|---:|---:|---:|
| Retained sudo.ws baseline | 851 | 10 | 0 | 861 |
| Rebuilt lean-sudo | 782 | 79 | 0 | 861 |

There are **71 remaining reference-pass / lean-fail findings**. The command
exited 1. The rebuilt sudo SHA-256 is
`5b3eebac28da9f10e454ba9f87e48afb472842c6d2e9f00fef76950d07b9e26f`;
visudo is unchanged. Complete raw results are in `external-postfix/`.

All four previous timeouts now terminate. The sudoedit signal-cleanup test
passes, including manual termination of editor, child and parent: both binaries
exit 143 and remove temporary edit files. The three PTY topology tests now fail
their process-name assertion, not a timeout: lean's monitor is named
`sudo --lean-sudo-helper`, so upstream's substring matcher omits it. A manual
process-tree observation confirms the original, monitor and command exist, with
the expected two PTYs, session leaders and foreground process groups. See
`manual-lifecycle.py` and `manual-lifecycle.json` in the output directory.

The remaining findings are grouped with confirmed manual Ubuntu 26.04
reproductions, exact commands, sudoers/PAM/editor inputs and both implementations'
raw output in `grouped-findings.json`. The linked reproduction scripts use only
real containers, binaries and PAM modules. These groups distinguish deliberate
fail-closed policy, test assumptions, diagnostic differences and functional
parity bugs; they do not equate every failed assertion with a security defect.

### Triage rerun

The 71 postfix findings were triaged: 45 were lean-sudo parity bugs, fixed with
regression tests in `tests.d/66-ext-*.sh` and `visudo-tests.sh` (`ext-visudo-*`)
that pass on both implementations. The rerun used the same retained sudo.ws
baseline:

```sh
SUDO_EXTERNAL_OUT="$PWD/integration/out/external-triage2" \
  integration/external/run.sh --lean-only .lake/Triage/final2
```

| Implementation | Passed | Failed | Timed out | Total |
|---|---:|---:|---:|---:|
| Retained sudo.ws baseline | 851 | 10 | 0 | 861 |
| lean-sudo (triage build) | 827 | 34 | 0 | 861 |

The 26 remaining reference-pass / lean-fail findings are all README deviations
(names are under `sudo::sudoers::` unless they start with `visudo::` or another
`sudo::` module):

* "Fail-closed by design", syntax errors (lean-sudo prints sudo.ws's diagnostics
  verbatim, then stops): `cmnd::command_specified_not_by_absolute_path_is_rejected`,
  `cmnd_alias::{cmnd_alias_cannot_start_with_underscore,
  command_specified_not_by_absolute_path_is_rejected, keywords}`,
  `env::{check,keep}::key_value_syntax_needs_double_quotes`,
  `host_alias::{host_alias_cannot_start_with_underscore, keywords}`,
  `runas_alias::keywords`, `user_list::{user_alias_cannot_start_with_underscore,
  user_alias_keywords}`, and the include loops `include::include_loop_not_fatal`,
  `includedir::{include_loop, statements_prior_to_include_loop_are_evaluated}`.
* "Fail-closed by design", insecure includes: `include::{ownership_check_not_fatal,
  permissions_check_not_fatal}`, `includedir::{ignores_and_warns_about_file_with_bad_ownership,
  ignores_and_warns_about_file_with_bad_perms, ignores_directory_with_bad_ownership,
  ignores_directory_with_bad_perms}`.
* "Fail-closed by design", undefined aliases and cycles:
  `cmnd_alias::unlisted_cmnd_fails`, `visudo::flag_strict::{alias_cycle, undefined_alias}`.
* "Other differences": canonical exec path
  (`sudo::path_search::arg0_script_is_passed_from_commandline`, upstream-ignored gh735) and
  `SUDO_PS1` starting with `() ` (`sudo::sudo_ps1::{can_start_with_parentheses,
  ps1_is_set_even_if_sudo_ps1_fails_the_env_keep_check}`).

## Sanitizer and generated-C coverage builds

```sh
integration/build-variant.sh sanitize
integration/coverage/run.py sanitize --no-build
integration/coverage/run.py asan
integration/coverage/run.py coverage
```

Each runner executes both complete Docker suites, preserving their ordinary
setuid installation, real services and existing capabilities. Variants have
independent architecture-qualified Docker caches and export binaries into
`.lake/linux-sanitize/`, `.lake/linux-asan/` and `.lake/linux-coverage/`.
`SUDO_IT_BASE` selects the build and suite base. Do not run the same variant
concurrently in one checkout. `--no-build` reuses its existing binary artifacts.

The trap sanitizer uses Clang `-fsanitize=undefined,bounds -fsanitize-trap=all`
on `c/*.c`; it requires no sanitizer runtime. The separate ASan build instruments
that same C boundary and links Clang's AddressSanitizer runtime. LeakSanitizer is
disabled by a harness-only linked options object because the suite exercises
setuid and ptrace; this variant therefore makes no leak-detection claim. Neither
variant instruments the prebuilt Lean runtime or external libraries.

Outputs live in `integration/out/<variant>/`: verbatim suite console logs, TAP
and detailed per-test logs, plus `results.json` containing suite statuses,
verbatim summary lines and crash/sanitizer diagnostics with reproducing test
names. Any suite failure or matched crash diagnostic makes the runner fail.
Signal diagnostics are leads requiring classification: a deliberately signalled
test command is not automatically a sanitizer defect. Silence is not proof that
no process died: the suite's assertions remain the primary behavioral oracle.

Coverage uses GCC gcov on the trusted C layer and all locally generated Lean C,
with atomic counter increments and unoptimized generated code. The coverage-only
linker wrappers in `integration/coverage/flush.c` dump and reset counters before
`execve`, `fexecve`, `_exit` and `_Exit`. Normal exit uses gcov's ordinary handler.
They are never linked into product or sanitizer binaries. The runner precreates
writable counter files inside each isolated container so setuid-root, root and
credential-dropped helpers can update the same locked gcov records despite
different umasks. No environment variable must survive sudo's environment filter.
A harness-only constructor opens `/coverage` with `O_CLOEXEC`; the coverage
`open` wrapper redirects only `/coverage/` paths through `openat` on that
directory. Thus a helper can flush after chroot and dropping privileges without
requiring `/proc` or a writable host-visible path inside its new root. The
descriptor closes on exec and is recreated when an instrumented helper starts.
It copies counters out before removing the sudo container, carries them into the
visudo container, and copies them out again after that suite. Move the existing
`integration/out/coverage/data/` aside before a fresh coverage run.

The report image uses the exact build's gcov version and `.gcno` notes.
`integration/out/coverage/coverage.json` contains every instrumented C function,
generated Lean function, line counter and module total; `coverage.md` highlights
unexecuted security boundaries in priority order. `gcov.log` retains tool
diagnostics, and `.lake/linux-coverage/notes/` preserves generated C and notes.
Lean function names are the generated symbols; their line numbers refer to
generated C, not original Lean source positions. Compiler-erased proofs and
inlined Lean declarations have no independent runtime counter. Forked processes
can inherit counters, so frequencies are not exact call counts; hit/miss coverage
is the intended evidence. Abrupt fatal signals can still lose counters.
The JSON also groups Lean symbols by their owning declaration, merging boxed,
reduced-argument and specialised variants. These symbol-derived groups are an
approximation, not an exact source map; they distinguish an unused generated
wrapper from a declaration whose variants were all unexecuted.

Coverage-only flushing can allocate and perform I/O at execution boundaries,
including a post-fork helper. Its extra directory descriptor intentionally
retains access to counter files outside a chroot until exec. This changes timing,
descriptor activity and process authority: coverage binaries are not evidence
of production async-signal safety, descriptor isolation or chroot confinement.
Treat instrumentation-induced suite differences separately from product bugs.
Unexecuted credential transitions, authentication-cache checks, helper protocol
validation and privileged file copy-back are highest-priority gaps; unexecuted
plugin, interception, remote logging and supervision failures remain important
even where their normal success paths are covered.

### Recorded instrumented full-suite run

The 2026-10-25 arm64 run, rebuilt after the proof-audit product changes, recorded
these identical summaries for trap-sanitized, ASan and coverage binaries:

```text
# passed: 918/918, failed: 0
# passed: 154/154 (skipped: 0), failed: 0
```

Both sanitizer result files contain zero findings. That baseline coverage run also
contained zero runtime diagnostics and collected 108 nonempty counter files.

`99c-fault-paths.sh` was then added for the unexecuted failure paths below. Its
effect was measured twice. First, the unchanged coverage binary ran the full suites
with the first 32 fault-path cases (950 sudo cases): C functions 710/926, C lines
2318/2783, Lean functions 5029/11619, Lean lines 162243/362383, groups 1676/3251.
Then the coverage variant was rebuilt after the integrator's timestamp process
identity change and run with 36 fault-path cases (954 sudo cases, 933 passing; all
21 failures are `fault-*` implementation differences). The visudo suite in that run
passed 155/176; its 21 failures are in-progress `ext-visudo-*` cases from another
change, not this module. The 37th case, `fault-audit-json-list-and-validate`, was
accumulated into the same counter files by a filtered run of the same binary.
Both full runs had zero runtime diagnostics.

| Instrumented code | Baseline functions | Baseline lines | With fault paths: functions | With fault paths: lines |
|---|---:|---:|---:|---:|
| Trusted C | 701/926 | 2293/2783 | 727/926 | 2365/2783 |
| Generated Lean C | 4989/11619 | 160624/362383 | 5080/11619 | 163943/362545 |

Symbol-derived Lean declaration groups rose from 1665/3251 to 1687/3251. These
figures include generated variants and dormant declarations; they are not
source-level branch coverage percentages or a claim that every zero-count symbol
is reachable. The full report is `integration/out/coverage/coverage.md`, with
machine-readable records in `coverage.json` beside it. The baseline report is
kept in `integration/out/coverage-before-faults/` and the same-binary comparison
in `integration/out/coverage-faults-samebinary/`.

Newly executed groups: `Exec.fcntlSweepAccepted`, `Exec.warnLimit` and the
`cloexecFrom` specialisation of `sweepDescriptors`/`completeSweep` (3.1 million
fallback descriptor visits); `Pam.pamChauthtok`, `Pam.erasePassword`,
`Pam.pamStrerror`; `PluginHost.checkSubcommand`, `subcommandInfo`, `accept`,
`disable` and `auditError`; `Callbacks.eventOperation`, `validEvent`,
`validEventPlan`, `modifyEvent` and `error`; `LogSrv.resolverHelper` and
`tlsInitError`; timestamp `failure`. Newly executed C functions include the
approval `check` trampoline, the event trampolines (`event_alloc`, `event_set`,
`event_add`, `event_del`, `event_setbase`, `event_free`, `dispatch`),
`ls_logprim_resolve` and `lean_pam_strerror`.

Still unexecuted, with the reason no real end-to-end scenario reaches them here:

1. **Plugin conversation and hooks:** `Callbacks.converse`, `clearReplies`,
   `register`, `Pam.pluginReadReply` and the C `conversation`, `register_hook` and
   `deregister_hook` trampolines. The only upstream code that prompts through the
   plugin conversation or registers environment hooks is a policy plugin
   (`sudoers_policy`, upstream `sample_policy`); lean-sudo implements policy itself
   and refuses policy plugins. Ubuntu ships no `python_plugin.so`, and `sudoers_io`,
   `sudoers_audit`, `audit_json`, `sample_io`, `sample_approval` and the group
   plugins never call the conversation or hook interfaces.
2. **AppArmor profile switching:** `Exec.apparmor` needs AppArmor in the kernel;
   the Docker Desktop VM kernel exposes no AppArmor LSM, so `exec-apparmor-*`
   takes its disabled branch.
3. **Resolver address serialization:** `LogSrv.resolverNodes`/`resolverWrite` and
   `ls_logprim_address` run whenever a log-server host name resolves (the
   `localhost` TLS cases depend on it), but the parent kills the helper after
   reading its final frame, before gcov's exit-time flush.
4. **Generic or proof-only symbols:** the unspecialised `sweepDescriptors` and
   `completeSweep`, `commandDescriptorOpen`, `commandAuthorized`,
   `validSubmitIndex` and timestamp `call` are inlined, specialised or used only
   by proofs; their executing copies are counted under other symbols.
5. **Terminal job control during a password prompt:** the PAM suspend/resume
   callbacks (`lean_pam_kill`, `lean_pam_getpid`, `lean_pam_callback_call`) need a
   job-control shell stopping and continuing sudo at the prompt; no case does so
   yet.

Earlier coverage harness attempts are retained under `integration/out/coverage-*`
for diagnosis. Their path-permission/chroot/stale-descriptor diagnostics were
harness defects, not sanitizer findings; only the final `coverage/` directory
supplies the current figures above.
