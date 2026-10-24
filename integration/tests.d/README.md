# Scenario files

`tests.sh` sources every `*.sh` file here, in name order, after its built-in tests.
Each file is a list of `begin NAME && { …; end; }` blocks using the harness in
`tests.sh` (`run`, `pty`, `expect_*`). Tests may write their own sudoers fragments
(`install -m 0440 /dev/stdin /etc/sudoers.d/x <<'EOF' … EOF`); `reset_state` restores
`/etc/sudoers` and `/etc/sudoers.d` before every test.

Spare users without rules (password = name + `pw`): ivan, judy, kate, liam, mona, nick,
olga, pete.

Every test must pass against the reference: `integration/run.sh reference 'name-regex'`.
