# End-to-end sudo and visudo suites (Docker)

The sudo suite installs an implementation as the real setuid-root
`/usr/bin/sudo`, with `/usr/bin/sudoedit -> sudo`, in a throwaway Ubuntu 26.04
container. It exercises that binary as unprivileged users and root. The reference
is Ubuntu's sudo.ws 1.9.17p2 (`/usr/bin/sudo.ws`), not the distribution's default
`sudo` alternatives link. The separate visudo suite runs the selected visudo
against the same container fixtures.

Current full-suite results:

| Suite | sudo.ws | lean-sudo |
|---|---:|---:|
| sudo | 728/728 | 728/728 |
| visudo | 154/154 | 154/154 |

These are shared compatibility suites, not a claim that every behavior is
identical: intentional safety differences are encoded in the expectations.
Ubuntu's sudo-rs remains an optional comparison target for the sudo suite; no
current pass count is claimed for it.

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
`--hostname sudo-it --network none --cap-add SYS_PTRACE --cap-add SYS_ADMIN`. Only
`integration/out/` is mounted, writable; host binaries and the visudo harness are
copied in. The container is removed on runner exit. `SYS_PTRACE` allows the audit
cases to use `strace` across credential transitions and inspect actual Linux
`USER_CMD` netlink records. `SYS_ADMIN` lets both sudo implementations install
their exec-interception seccomp filter without `no_new_privs`, which would change
set-ID command semantics. No host audit daemon or `AUDIT_CONTROL` capability is
required. Tests also capture syslog datagrams locally rather than requiring a
running syslog service.

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
| `56-nsswitch.sh` | `nsswitch-*`: sudoers source parsing/defaults/order, unavailable SSSD, no implicit local-policy fallback, empty/unknown-source safety expectations. |
| `57-shell-residual.sh` | `shell-residual-*`: noninteractive authentication, visible passwords, EOF/interrupt accounting, file/syslog/audit events, real GID, dot/PATH lookup and timestamp scope/invalidation. |
| `58-command-lookup.sh` | `command-lookup-*`: runas-first lookup, invoker fallback, private directories, execute-bit/nonregular checks, list resolution and terminal dot-search results. |
| `58-sudoedit-parity.sh` | `sudoedit-parity-*`: temporary names/mtime, size/mtime copyback decisions, multi-file failures, editor selection/PATH/quoting/injection and diagnostic prefixes. |
| `59-shell-policy.sh` | `shell-policy-*`: unknown-identity error/event ordering, shell versus sudoedit authorization, non-generic PAM challenges and relative-command spelling/logging. |
| `60-exec.sh` | `exec-*`: resource limits, closed stdin, cwd failures, NOEXEC, timeouts/escalation, background/pty lifecycle, AppArmor, utmp, stay_setuid, signal relay and job control. |
| `61-timestamp-interop.sh` | `timestamp-interop-*`: bidirectional sudo.ws credential sharing, exact v2 layout, tty/ppid isolation, timeout and `-k`/`-K`, configured directory/owner, malformed and foreign records. |
| `70-iolog.sh` | `iolog-*`: unmodified `sudoreplay.ws` interoperability, input/output streams, compression, permissions, error policy, path expansion, sequence wrap and password masking. |
| `80-i18n.sh` | `i18n-*`: byte-for-byte German/French/C diagnostics, help/listing/prompts, LANGUAGE precedence, missing-locale fallback and literal configured messages. |
| `85-jsonlog.sh` | `jsonlog-*`: json/json_compact/json_pretty file and syslog records for acceptance, denial, authentication rejection, exit/signal, runas group, repeated events and I/O-log linkage. |
| `95-coverage.sh` | `coverage-*`: differential CLI, authentication/listpw/verifypw, timestamps, umask, shell/cwd/environment, listing, sudoedit, signal and job-control matrices. |
| `96-sssd.sh` | `sssd-*`: real LDAP/SSSD roles, allow/deny/negation, runas, signed sudoOrder, global/role options, argument wildcards, short/long listings and NSS source/action ordering. |
| `97-group-plugin.sh` | `group-plugin-*`: shipped group_file/system_group providers, named/numeric membership, negation, aliases/runas/Defaults/listing, always_query_group_plugin and loader/init/ABI failures. |
| `98-logsrv.sh` | `logsrv-*`: real sudo_logsrvd TCP/TLS events and I/O, generated CA/client credentials, trust/identity failures, unreachable-server policies, failover, final commits, live disconnect/restart failure policy and serialized intercepted subcommands. |

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

The integrity cases assert that insecure grants never take effect and check the
diagnostic; syntax-error cases allow either reference recovery or fail-closed
refusal. The group-writable include case specifically uses a non-root group.
The NSS module explicitly branches its empty/unknown-source expectations by
implementation, and visudo's alias cases encode its stricter validation rather
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

Lean-sudo's visudo rejects undefined/cyclic aliases even without `-s`, including
invalid unused definitions, to avoid installing policy its runtime would refuse.
Reference comparisons use strict mode where appropriate; unused-invalid-alias
cases assert the intentional difference explicitly. Rejected edits retain the
existing policy on `x`/EOF, while the deliberately dangerous `Q` override remains
available.
