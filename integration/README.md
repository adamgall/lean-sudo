# End-to-end sudo suite (Docker)

Installs a sudo implementation as the real setuid-root `/usr/bin/sudo` (plus
`/usr/bin/sudoedit -> sudo`) in a throwaway Ubuntu 26.04 container and drives it
as unprivileged users. The same tests run against the original sudo.ws (the
reference), Ubuntu's sudo-rs, and our Lean binary.

```
integration/run.sh reference                  # sudo.ws 1.9.17p2 (must pass 100%)
integration/run.sh sudo-rs                    # optional comparison
integration/run.sh .lake/build/bin/sudo       # any sudo binary on the host
integration/run.sh .lake/build/bin/sudo 'tty-|env-'   # ERE filter on test names
```

Output is TAP (`ok N - name` / `not ok N - name` + `#` diagnostics with expected
vs. actual, the command, exit status, stdout and stderr), a summary, and exit
status 0 only if every selected test passed (1 = failures, 2 = setup error or
no test matched). Full per-test transcripts: `integration/out/<label>.log`, TAP
copy: `integration/out/<label>.tap`, image build log: `integration/out/build.log`.

Requirements: docker (the invoking user in the `docker` group). Variables:
`SUDO_IT_BASE` (base image; default `ubuntu:26.04`, falls back to
`ubuntu:devel` if that build fails), `SUDO_IT_IMAGE` (tag, default
`lean-sudo-it`).

### Building the Linux executables on macOS

```
integration/run.sh --build                    # build sudo/visudo, then run the sudo suite
integration/run.sh --visudo .lake/linux/visudo
```

`integration/build.sh` builds the current working tree in an arm64 Ubuntu 26.04
container and exports the Linux binaries to `.lake/linux/`. Pure Lean modules and
the entry point can be type-checked natively with `lake build LeanSudo` followed
by `lake env lean Main.lean`; do not build the Linux C shim natively on macOS.

### IO shell boundaries

`Main.lean` delegates to `LeanSudo.Shell`: it collects account/process facts,
loads and validates sudoers, resolves command paths without changing the executable
name, then executes `Core.decide`'s result. Authentication is rechecked under the
timestamp-file lock; successful authenticated requests refresh the cache only
after PAM account management succeeds for execution/editing. PAM credentials and
sessions are bracketed around command execution, including failure paths. PAM
unavailability is fatal even for NOPASSWD execution.

Linux `/proc/self/cmdline` supplies the original argv[0] (so the `sudoedit` symlink
is preserved) and raw bytes for UTF-8 validation. In addition to invalid raw UTF-8,
the shell conservatively refuses a decoded U+FFFD replacement character, including
a deliberately supplied valid U+FFFD. Invalid UTF-8 environment entries are dropped
by the existing Sys interface. An unreadable process identity also fails closed
instead of creating timestamp entries that could survive PID reuse. Unsupported
Defaults warnings for known ignored settings, such as Ubuntu's `mail_badpass`,
are suppressed; unsupported security-relevant settings still fail validation.

These boundaries retain the documented fail-closed syntax-error deviation from
sudo.ws. No sudo test expectations were changed for the IO shell. The visudo
suite's `STOCK_OK` list is now derived from eligible files in `/etc/sudoers.d`,
using sudo's filename exclusions. The alias-denial regression added `gina`, but
the three exact-output stock-policy checks had not been updated. Both
implementations correctly report the extra parsed file; this fixes a stale test
expectation and also accommodates the sudoedit fixtures without weakening the
exact-output assertion.

## How it works

* `Dockerfile` installs `sudo` (sudo.ws, shipped as `/usr/bin/sudo.ws` on
  Ubuntu ≥ 25.10), `sudo-rs`, `python3`, `procps`, `util-linux`, PAM; creates
  the users; installs the fixtures from `sudoers.d/` (root:root 0440) next to
  Ubuntu's stock `/etc/sudoers` and checks them with `visudo.ws -c`.
* `run.sh` builds the image (layer cache: only the last layers change when
  `tests.sh`/`ptyrun.py` change), `docker create`s a container with
  `--network none`, `docker cp`s a host binary in (for a path argument), and
  starts it. Only `integration/out/` is mounted (writable); nothing else from
  the host.
* `tests.sh` (container entrypoint, runs as root) installs the binary as
  `/usr/bin/sudo` root:root 4755, then runs each test after resetting state
  (timestamp dirs of sudo.ws/sudo-rs/lean-sudo, `/etc/sudoers`,
  `/etc/sudoers.d`). Non-tty commands run via
  `env -i … setpriv --reuid --regid --init-groups -- sh -c …` (no controlling
  tty, stdin `/dev/null`, cwd = home). Tty tests use `ptyrun.py`, which runs the
  snippet as the user as session leader of a fresh pty and scripts it
  (`-e REGEX` wait for output, `-s TEXT` type after a 0.1 s pause).
  Every command has a 40 s timeout.

Users (password = name + `pw`): `alice` (group `sudo` ⇒ `%sudo ALL=(ALL:ALL) ALL`),
`bob` (no rights), `carol`, `dave`, `erin`, `frank`, `gina` — rules in `sudoers.d/`.

## Scenarios

| Test | Asserts |
|---|---|
| alice-stdin-password | `-S` correct password ⇒ `id -u` = 0, `-S` prompt on stderr |
| alice-wrong-password-three-times | 3 bad passwords ⇒ exit 1, `Sorry, try again.`, `3 incorrect password attempts` |
| alice-wrong-then-right-password | retry succeeds |
| alice-noninteractive-without-timestamp | `-n` ⇒ exit 1 `a password is required` |
| alice-no-tty-no-stdin-flag | no tty, no `-S` ⇒ exit 1 `a terminal is required` |
| root-needs-no-password | root `-n` works |
| bob-not-in-sudoers / bob-noninteractive-denied | exit 1, `bob is not in the sudoers file` (tolerant for `-n`) |
| alice-runas-other-user / -group / -uid-hash | `-u bob`, `-g adm`, `-u '#0'` |
| carol-nopasswd-id / -whoami / -double-dash | NOPASSWD rules, `--` |
| carol-cat-denied / carol-cat-noninteractive-denied | `is not allowed to execute` |
| carol-runas-bob-with-password / -needs-password | `(bob) /usr/bin/id` needs a password |
| carol-runas-alice-denied | runas not permitted |
| dave-su-denied / dave-shell-alias-denied / dave-id-allowed | `ALL, !/usr/bin/su, !SHELLS` |
| gina-alias-inner-deny / -inner-allow / -other-command-allowed-by-all | `ALL, LIMITED` with `LIMITED = /usr/bin/id, !/usr/bin/whoami`: the alias's inner `!` denies whoami despite the earlier `ALL` |
| erin-group-only-runas / erin-user-and-group-denied | `(:adm)` rule: gid adm, uid erin; `-u root -g adm` denied |
| frank-* | exact args, other args, missing args, `/tmp/*` glob, `""` (no args) |
| unknown-runas-user | `unknown user nosuchuser` |
| command-not-found | `nosuchcmd: command not found` |
| chdir-option-not-permitted | `-D /tmp` ⇒ `you are not permitted to use the -D option` |
| exit-status-propagation | `sh -c 'exit 42'` ⇒ 42 |
| signal-death-propagation | `kill -TERM $$` ⇒ invoking shell sees 143 |
| env-reset-drops-user-vars, env-secure-path, env-sudo-variables, env-sudo-command-with-args, env-target-identity(-other-user) | env_reset, `PATH` = secure_path, `SUDO_USER/UID/GID/COMMAND`, `HOME/USER/LOGNAME` of target |
| env-ld-preload-dropped | `LD_PRELOAD`/`LD_LIBRARY_PATH` never reach the command |
| env-E-denied-without-setenv / env-var-arg-denied-without-setenv | carol: `not allowed to preserve the environment` / `not allowed to set the following environment variables: FOO` |
| env-E-allowed-for-ALL-command | alice `-E` allowed (SETENV implied by `ALL`) |
| env-E-with-setenv-keeps-safe-vars / env-E-still-drops-dangerous-vars / env-var-arg-with-setenv | erin SETENV: `FOO` kept, `HOME` of invoker kept; `LD_*`, `BASH_ENV`, `PYTHONPATH`, `PERL5OPT`, `BASH_FUNC_*` dropped |
| list-alice, list-carol, list-carol-command(-path-search/-denied) | `-l` output, `-l cmd` prints the full path, exit 1 if not allowed |
| tty-prompt-and-no-echo | `[sudo] password for alice:` on the tty, password not echoed |
| tty-wrong-then-right, tty-no-password-required-for-nopasswd | tty retry; NOPASSWD never prompts |
| tty-validate-then-noninteractive, tty-timestamp-reused-without-prompt | `-v` then `-n` in one session; one prompt per session |
| tty-k-invalidates, tty-K-removes | `-k`/`-K` then `-n` ⇒ `a password is required` |
| tty-timestamp-is-per-tty | a second pty session must ask again |
| login-shell-i, login-shell-i-is-login-shell | `-i`: cwd and HOME `/root`, bash login shell |
| shell-s-runs-SHELL, shell-s-interactive | `-s` runs `$SHELL -c …` / `$SHELL` |
| help-exit-0, version-exit-0, usage-error-no-args | `-h`/`-V` exit 0; no args ⇒ exit 1 `usage: sudo` |
| sudoers-* | syntax errors, world/group-writable or non-root-owned files (see below) |
| binary-without-setuid-bit | non-setuid copy refuses to run |

## Reference behaviour that differs from the original brief

All observed with sudo.ws 1.9.17p2 on Ubuntu 26.04; the tests assert these.

1. **Packaging.** Ubuntu 26.04's `/usr/bin/sudo` is an alternatives link to
   sudo-rs; the package `sudo` ships sudo.ws as `/usr/bin/sudo.ws`. That binary
   is the reference.
2. **Authentication comes before denial.** sudo.ws asks for the password before
   saying "not in the sudoers file" / "not allowed to execute" (unless the
   command matched a NOPASSWD rule), and before "command not found" and the
   `-D` refusal. Hence with `-n` such requests fail with `a password is
   required`. Deny tests therefore supply the password via `-S`; the `-n`
   variants accept either message.
3. **Syntax errors do not stop sudo.** sudo.ws reports
   `/etc/sudoers.d/zz-bad:1:9: syntax error` (with a caret line) and then
   *recovers*: valid entries — even other lines of the broken file — still
   apply, and the command runs (exit 0). Same for a syntax error in
   `/etc/sudoers` itself. The tests only require the error to be reported and
   accept either running or refusing (exit 1), so a fail-closed implementation
   passes.
4. **Insecure files in `sudoers.d` are skipped, not fatal.** A world-writable
   include prints `<file> is world writable`; a non-root owner prints
   `<file> is owned by uid N, should be 0`; a group-writable file whose group is
   not root prints `<file> is owned by gid N, should be 0`. The file is
   ignored and the rest of the policy still applies. A group-writable file
   with group root is accepted silently (not tested; DESIGN.md's fail-closed
   rule is stricter). A world-writable `/etc/sudoers.d` directory is skipped
   as a whole. Tests assert the grant inside the bad file never takes effect
   and the warning is printed; refusing outright also passes.
5. **`/etc/sudoers` itself** world-writable or not root-owned ⇒ refuses
   (exit 1) with `/etc/sudoers is world writable` /
   `/etc/sudoers is owned by uid N, should be 0` (followed by
   `error initializing audit plugin sudoers_audit`).
6. **Missing setuid bit**: sudo.ws says
   `<path> must be owned by uid 0 and have the setuid bit set`; the
   `effective uid is not 0, is … nosuid …` message only appears when the binary
   *is* setuid root but euid ≠ 0 (nosuid mount). The test accepts both.
7. **`LD_PRELOAD`**: glibc's secure-execution mode already strips `LD_PRELOAD`,
   `LD_LIBRARY_PATH`, … from a setuid program's environment, so that check is
   partly vacuous; `env-E-still-drops-dangerous-vars` also checks variables
   only sudo's own `env_delete` list removes (`LD_FOO`, `BASH_ENV`,
   `PYTHONPATH`, `PERL5OPT`, `BASH_FUNC_*%%`). Note: with SETENV, an explicit
   `sudo LD_PRELOAD=x cmd` on the command line *does* pass in sudo.ws
   (SETENV allows otherwise-forbidden variables); not tested.
8. **`-E` and `ALL`**: alice may use `-E` because SETENV is implied for a
   command matched by `ALL`; the "`-E` denied without SETENV" case uses carol.
   With `-E`, `HOME` stays the invoking user's.
9. **Extra variables**: sudo.ws also sets `SUDO_HOME` (invoker's home), `MAIL`,
   and `TERM=unknown` when `TERM` is unset (not asserted).
10. **Timestamps without a tty** are scoped to the parent process (ppid), so a
    second `sudo` from the same non-tty shell does not prompt. Tests do not
    rely on this.
11. **Coreutils are uutils symlinks** (`/usr/bin/id -> ../lib/cargo/bin/coreutils/id`).
    sudo.ws matches the resolved command *path* (`/usr/bin/id`) against the
    rule; an implementation that compares `realpath`s would fail carol/frank.
12. **`-l cmd` not allowed**: exit 1 with no output at all.
13. **No terminal and no `-S`**: prints both `a terminal is required to read the
    password; …` and `a password is required`.
14. `--network none` leaves the container hostname unresolvable (sudo.ws then
    warns `unable to resolve host`); `tests.sh` adds an `/etc/hosts` entry.
15. `-s` quoting of the command for `$SHELL -c` is an implementation detail;
    the test uses a fake `$SHELL` that echoes its arguments and only checks the
    `-c hello` prefix.

## sudo-rs (informational)

`run.sh sudo-rs` passes 34/78: sudo-rs rejects frank's `/usr/bin/ls /tmp/*`
(wildcards in arguments), and uses different messages throughout
(`[sudo: authenticate] Password:`, `I'm sorry carol. I'm afraid I can't do
that`, `interactive authentication is required`, …).

## visudo suite

```
integration/run.sh --visudo reference                 # sudo.ws's /usr/sbin/visudo.ws (44 pass, 3 skipped)
integration/run.sh --visudo .lake/build/bin/visudo    # lean-sudo's visudo
integration/run.sh --visudo .lake/build/bin/visudo 'edit-'
```

Same image; `run.sh` copies `visudo-tests.sh` and the binary into the
container and uses the script as entrypoint. It runs visudo directly as root
(`env -i`, scripted `$EDITOR`s that append a line, do nothing, empty the file
or wait for a release file; `What now?` answers on stdin) and restores
`/etc/sudoers{,.d}` before every test. Logs: `out/visudo-reference.*`,
`out/custom-visudo.*`.

Covered: `-c` on the stock policy (exact `parsed OK` lines), `-c -q`, `-f -`,
syntax errors in `/etc/sudoers` and in `sudoers.d`, wrong owner/mode
(checked by default, only with `-O`/`-P` when `-f` is given), missing
`@include`, duplicate aliases, bad/unknown `Defaults`; edit mode: valid
append installed `0440 root:root`, syntax/semantic error then `x`, EOF, `e`
then `x`, unknown answer, `Q` (installs anyway), unchanged file, zero-length
file, `$EDITOR` words and the `--` before the file, `SUDO_EDITOR` precedence,
missing editor, `!env_editor` + `editor` list, no usable editor, a second
visudo while the first one's editor runs (busy), `-f` new file, `-f` keeps
owner/mode unless `-O`, non-root refused; `-h`, `-V`, usage errors.

Observed sudo.ws visudo behaviour the tests encode: `x`/EOF/`Q` exit 0;
unchanged ⇒ `visudo: /etc/sudoers.tmp unchanged`, exit 0; the editor's exit
status is ignored; `-I` does not affect `-c`; unreadable `sudoers.d` entries
are warned about and skipped. lean-sudo-only tests (skipped for the
reference): its lock (`F_OFD_SETLK`) and sudo.ws's `fcntl` lock exclude each
other in both directions, and a stale `/etc/sudoers.tmp` means busy (sudo.ws
truncates and reuses it). Deliberate difference: undefined aliases, alias
cycles and `Defaults` lean-sudo refuses (e.g. `noexec`) are errors (sudo.ws
warns or accepts), because lean-sudo's `sudo` would refuse such a policy.
