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
* `SUDO_IT_IMAGE`: suite image tag; defaults to `lean-sudo-it`.

`integration/build.sh` builds Linux `sudo` and `visudo` from the working tree
using `integration/Dockerfile.build` and Docker's local artifact output, exporting
both to `.lake/linux/`. It works on macOS and Linux; the script does not force an
arm64 platform. `--build` invokes it before running the selected suite. The build
script also accepts `SUDO_IT_BASE` (default `ubuntu:26.04`, without the suite's
fallback). Its log is `integration/out/linux-build.log`.

Output is TAP (`ok N - name` / `not ok N - name`), diagnostics and a summary.
The harness exits 0 when all selected tests pass, 1 for test failures, and 2
for a missing input binary or no matching tests; runner usage/image-build errors
also exit 2. Full transcripts and TAP copies are written to
`integration/out/<label>.log` and `.tap`; the suite image build log is
`integration/out/build.log`. Standard labels are `reference`, `sudo-rs`,
`custom-sudo`, `visudo-reference` and `custom-visudo`. Other custom binary
basenames affect the label. Logs are assigned to the invoking host UID/GID.

## Container and harness

`Dockerfile` installs sudo.ws, sudo-rs, Python, procps, util-linux, account/PAM
tools, `strace`, OpenLDAP (`slapd`, `ldap-utils`), SSSD and its LDAP/sudo/NSS
libraries. It also installs `locales`, `language-pack-de-base` and
`language-pack-fr-base`, and generates `de_DE.UTF-8` and `fr_FR.UTF-8`.
Translation tests assert actual German/French text as well as reference equality,
so missing catalogs cannot silently turn them into English-only comparisons.

The image installs `sudoers.d/` fixtures as root:root 0440 alongside Ubuntu's
stock policy and validates them with `visudo.ws -c`. It copies `tests.sh`,
`ptyrun.py`, all `tests.d/` modules and the vendored `sudo-schema.ldif`.

`run.sh` builds the image and creates a container with
`--hostname sudo-it --network none --cap-add SYS_PTRACE --cap-add SYS_ADMIN`
and `--cap-add SYS_RESOURCE`. Only
`integration/out/` is mounted, writable; host binaries and the visudo harness are
copied in. The container is removed on runner exit. `SYS_PTRACE` allows the audit
cases to use `strace` across credential transitions and inspect actual Linux
`USER_CMD` netlink records. `SYS_ADMIN` lets both sudo implementations install
their exec-interception seccomp filter without `no_new_privs`, which would change
set-ID command semantics. No host audit daemon or `AUDIT_CONTROL` capability is
required: strace observes real kernel audit traffic, not a replacement audit
service. Likewise, utmp readers and inotify are observation tools, not mocks.
`SYS_RESOURCE` preserves normal root resource-limit privileges: both implementations
temporarily raise `RLIMIT_NPROC` around the UID switch and restore it before exec.
Docker otherwise denies that raise when the caller lowered the hard limit, causing
the Lean runtime's additional threads to trigger Linux's `PF_NPROC_EXCEEDED` check.

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
| `64-helper-mode.sh` | `helper-mode-refuses-*`: an unprivileged caller who runs `sudo --lean-sudo-helper` with a socketpair or pipe of their own on descriptor 63, directly or beneath a waiting sudo process, gets the ordinary usage error and the forged root plan never runs. |
| `70-iolog.sh` | `iolog-*`: unmodified `sudoreplay.ws` interoperability, input/output streams, compression, permissions, error policy, path expansion, sequence wrap and password masking. |
| `80-i18n.sh` | `i18n-*`: byte-for-byte German/French/C diagnostics, help/listing/prompts, LANGUAGE precedence, missing-locale fallback and literal configured messages. |
| `85-jsonlog.sh` | `jsonlog-*`: json/json_compact/json_pretty file and syslog records for acceptance, denial, authentication rejection, exit/signal, runas group, repeated events and I/O-log linkage. |
| `95-coverage.sh` | `coverage-*`: differential CLI, authentication/listpw/verifypw, timestamps, umask, shell/cwd/environment, listing, sudoedit, signal and job-control matrices. |
| `96-sssd.sh` | `sssd-*`: real LDAP/SSSD roles, allow/deny/negation, runas, signed sudoOrder, global/role options, argument wildcards, short/long listings and NSS source/action ordering. |
| `97-group-plugin.sh` | `group-plugin-*`: shipped group_file/system_group providers, named/numeric membership, negation, aliases/runas/Defaults/listing, always_query_group_plugin and loader/init/ABI failures. |
| `98-logsrv.sh` | `logsrv-*`: real sudo_logsrvd TCP/TLS events and I/O, generated CA/client credentials, trust/identity failures, unreachable-server policies, failover, final commits, live disconnect/restart failure policy and serialized intercepted subcommands. |
| `99b-plugins.sh` | `plugin host`: shipped audit_json event structure/status and policy rejection, upstream sample I/O binary/terminal streams, loader diagnostics and upstream plugin version output. |

The plugin build stage downloads sudo 1.9.17p2 and checks the SHA-256 published
on [sudo.ws](https://www.sudo.ws/releases/stable/) before building its unmodified
`sample_plugin.so` and `sample_approval.so`. Tests also use Ubuntu's shipped
`audit_json.so`, `sudoers.so`, `group_file.so` and `system_group.so`.
The sample approval plugin's business-hours policy depends on the actual clock;
only its deterministic version interface is tested. Synthetic callback failures,
command-name approval rules and malformed log-server peers have no real substitute
and are not tested. No test-only plugin DSO is built or loaded.

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
