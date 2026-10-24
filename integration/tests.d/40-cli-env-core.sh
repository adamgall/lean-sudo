#!/bin/bash
# sudo.ws front-end, environment and decision-core compatibility.
cli_core_grant_bob() {
  printf 'bob ALL=(ALL:ALL) NOPASSWD: ALL\n' > /etc/sudoers.d/zz-cli-grant
  chmod 0440 /etc/sudoers.d/zz-cli-grant
}

begin cli-core-help-selinux && {
  run bob 'sudo -h'
  expect_rc 0
  expect_out_has '[-r role] [-t type]'
  expect_out_has '  -r, --role=role'
  expect_out_has '  -t, --type=type'
  end
}
begin cli-core-version-user && {
  run bob 'sudo -V'
  expect_rc 0
  expect_out_line 'Sudo version 1.9.17p2'
  expect_out_line 'Sudoers policy plugin version 1.9.17p2'
  expect_out_line 'Sudoers file grammar version 50'
  expect_out_line 'Sudoers I/O plugin version 1.9.17p2'
  expect_out_line 'Sudoers audit plugin version 1.9.17p2'
  expect_out_lacks 'Configure options:'
  end
}
begin cli-core-version-root && {
  run root 'sudo -V'
  expect_rc 0
  expect_out_has 'Configure options:'
  expect_out_line 'Sudoers path: /etc/sudoers'
  expect_out_line "Authentication methods: 'pam'"
  expect_out_line 'Default user to run commands as: root'
  expect_out_line 'Enable SELinux RBAC support'
  end
}
begin cli-core-selinux-disabled-options && {
  run root 'sudo -r fake_role -t fake_type /usr/bin/true'
  expect_rc 0
  end
}
begin cli-core-closefrom-default && {
  run root 'sudo -C 3 /usr/bin/true'
  expect_rc 0
  end
}
begin cli-core-closefrom-override && {
  printf 'Defaults closefrom_override\n' > /etc/sudoers.d/40-cli
  chmod 0440 /etc/sudoers.d/40-cli
  run root 'sudo -C 5 /usr/bin/true'
  expect_rc 0
  end
}
begin cli-core-closefrom-refusal && {
  run root 'sudo -C 5 /usr/bin/true'
  expect_rc 1
  expect_err_has 'you are not permitted to use the -C option'
  end
}
begin cli-core-host-run-refusal && {
  run root 'sudo -h elsewhere /usr/bin/true'
  expect_rc 1
  expect_err_has 'a remote host may only be specified when listing privileges'
  end
}
begin cli-core-host-list && {
  printf 'ivan elsewhere=(root) NOPASSWD: /usr/bin/true\n' > /etc/sudoers.d/40-cli
  chmod 0440 /etc/sudoers.d/40-cli
  run root 'sudo -l -h elsewhere -U ivan'
  expect_rc 0
  expect_out_has 'User ivan may run the following commands on elsewhere:'
  expect_out_has '/usr/bin/true'
  end
}
begin cli-core-edit-preserve-error-order && {
  run root 'sudo -e -E /etc/hosts'
  expect_rc 1
  expect_err_has 'usage: sudo'
  expect_err_lacks 'the -E option is not valid in edit mode'
  end
}
begin cli-core-chroot-warning && {
  run root 'sudo -R / /usr/bin/true'
  expect_rc 1
  expect_err_has 'the -R option will be removed in a future version of sudo'
  expect_err_has 'you are not permitted to use the -R option with /usr/bin/true'
  end
}
begin cli-core-timeout-refusal && {
  run root 'sudo -T 5 /usr/bin/true'
  expect_rc 1
  expect_err_has 'sorry, you are not allowed set a command timeout'
  end
}
begin cli-core-bell-stdin && {
  run alice 'echo alicepw | sudo -kBS /usr/bin/true'
  expect_rc 0
  expect_err_lacks $'\a'
  end
}
begin cli-core-prompt-environment && {
  run alice "echo alicepw | SUDO_PROMPT='site password: ' sudo -kS /usr/bin/true"
  expect_rc 0
  expect_err_has 'site password: '
  end
}
begin cli-core-prompt-option-priority && {
  run alice "echo alicepw | SUDO_PROMPT='wrong prompt: ' sudo -kS -p 'right prompt: ' /usr/bin/true"
  expect_rc 0
  expect_err_has 'right prompt: '
  expect_err_lacks 'wrong prompt:'
  end
}
begin cli-core-sudo-home && {
  cli_core_grant_bob
  run bob 'sudo -n /usr/bin/printenv SUDO_HOME'
  expect_rc 0
  expect_out_line '/home/bob'
  end
}
begin cli-core-sudo-tty-no-controlling-terminal && {
  cli_core_grant_bob
  run bob 'SUDO_TTY=forged sudo -n /usr/bin/env'
  expect_rc 0
  expect_out_lacks 'SUDO_TTY='
  end
}
begin cli-core-dpkg-colors && {
  cli_core_grant_bob
  run bob 'DPKG_COLORS=always sudo -n /usr/bin/printenv DPKG_COLORS'
  expect_rc 0
  expect_out_line 'always'
  end
}
begin cli-core-login-path && {
  printf 'Defaults !secure_path\n' > /etc/sudoers.d/40-cli
  chmod 0440 /etc/sudoers.d/40-cli
  useradd -m -s /bin/dash cli-login
  run root "PATH=/usr/bin:/bin:/opt/kept sudo -i -u cli-login /usr/bin/printenv PATH"
  expect_rc 0
  expect_out_line '/usr/bin:/bin:/opt/kept'
  end
}
begin cli-core-empty-shell && {
  cli_core_grant_bob
  run bob 'SHELL= sudo -ns /usr/bin/true'
  expect_rc 0
  end
}
begin cli-core-shell-noargs && {
  cli_core_grant_bob
  printf 'Defaults:bob shell_noargs\n' > /etc/sudoers.d/40-cli
  chmod 0440 /etc/sudoers.d/40-cli
  run bob "printf 'echo IMPLIED_OK\nexit\n' | sudo -n"
  expect_rc 0
  expect_out_line 'IMPLIED_OK'
  end
}
begin cli-core-shell-command-unescaped && {
  cli_core_grant_bob
  run bob 'sudo -ns /usr/bin/printenv SUDO_COMMAND'
  expect_rc 0
  expect_out_has ' -c /usr/bin/printenv SUDO_COMMAND'
  expect_out_lacks '\/usr'
  end
}
begin cli-core-login-bash-argv && {
  mkdir -p /usr/local/lib/cli-core
  printf '#!/bin/sh\nprintf "%%s\\n" "$@"\n' > /usr/local/lib/cli-core/bash
  chmod 0755 /usr/local/lib/cli-core/bash
  useradd -m -s /usr/local/lib/cli-core/bash cli-bash
  run root 'sudo -i -u cli-bash /usr/bin/true'
  expect_rc 0
  expect_out_line '--login'
  expect_out_line '-c'
  expect_out_has '\/usr\/bin\/true'
  end
}
begin cli-core-set-logname-disabled && {
  cli_core_grant_bob
  printf 'Defaults !set_logname, !env_reset\n' > /etc/sudoers.d/40-cli
  chmod 0440 /etc/sudoers.d/40-cli
  run bob 'sudo -n /usr/bin/printenv USER LOGNAME'
  expect_rc 0
  expect_out_line 'bob'
  end
}
begin cli-core-env-files && {
  cli_core_grant_bob
  printf 'SITE_VALUE=trusted\nDISPLAY=:9\n' > /etc/cli-env
  printf 'UNTRUSTED_VALUE=discarded\nLD_PRELOAD=/bad.so\n' > /etc/cli-restricted-env
  printf 'Defaults env_file=/etc/cli-env, restricted_env_file=/etc/cli-restricted-env\n' > /etc/sudoers.d/40-cli
  chmod 0440 /etc/sudoers.d/40-cli
  run bob 'sudo -n /usr/bin/env'
  expect_rc 0
  expect_out_line 'SITE_VALUE=trusted'
  expect_out_line 'DISPLAY=:9'
  expect_out_lacks 'UNTRUSTED_VALUE='
  expect_out_lacks 'LD_PRELOAD='
  end
}
begin cli-core-admin-flag && {
  rm -f /home/alice/.sudo_as_admin_successful
  run alice 'echo alicepw | sudo -kS /usr/bin/true; test -f "$HOME/.sudo_as_admin_successful"'
  expect_rc 0
  end
}
begin cli-core-list-other-admin && {
  run alice 'echo alicepw | sudo -kS -l -U carol'
  expect_rc 0
  expect_out_has 'User carol may run the following commands'
  end
}
begin cli-core-list-pseudocommand && {
  printf 'ivan ALL=(carol) NOPASSWD: list\n' > /etc/sudoers.d/40-cli
  chmod 0440 /etc/sudoers.d/40-cli
  run ivan 'sudo -n -l -U carol'
  expect_rc 0
  expect_out_has 'User carol may run the following commands'
  end
}
begin cli-core-list-verbose-command && {
  cli_core_grant_bob
  run bob 'sudo -n -ll /usr/bin/true'
  expect_rc 0
  expect_out_has 'Sudoers entry:'
  expect_out_has 'RunAsUsers:'
  expect_out_has '    Matched: /usr/bin/true'
  end
}
begin cli-core-cd-hint && {
  cli_core_grant_bob
  run bob 'sudo -n cd /'
  expect_rc 1
  expect_err_has '"cd" is a shell built-in command, it cannot be run directly.'
  expect_err_has 'the -s option may be used to run a privileged shell.'
  expect_err_has 'the -D option may be used to run a command in a specific directory.'
  end
}

begin cli-core-command-environment-cap && {
  run root 'long=$(printf "%05000d" 0); sudo /bin/sh -c '\''printf "%s" "$SUDO_COMMAND" | /usr/bin/wc -c'\'' "$long"'
  expect_rc 0
  expect_out_line 4104
  end
}
begin cli-core-version-root-exact && {
  run root '/usr/bin/sudo.ws -V > /tmp/cli-version-expected; sudo -V > /tmp/cli-version-actual; diff -u /tmp/cli-version-expected /tmp/cli-version-actual'
  expect_rc 0
  end
}

begin cli-core-timeout-compound && {
  cli_core_grant_bob
  printf 'Defaults:bob user_command_timeouts\n' >> /etc/sudoers.d/40-cli
  run bob 'sudo -n -T 1m2s /usr/bin/true'
  expect_rc 0
  end
}
begin cli-core-timeout-zero && {
  cli_core_grant_bob
  run bob 'sudo -n -T 0 /usr/bin/true'
  expect_rc 0
  end
}
begin cli-core-edit-dot-relative && {
  cli_core_grant_bob
  run bob 'cd /etc && SUDO_EDITOR=/usr/bin/true sudoedit -n ./hosts'
  expect_rc 0
  end
}
begin cli-core-edit-repeated-slash && {
  cli_core_grant_bob
  run bob 'SUDO_EDITOR=/usr/bin/true sudoedit -n /etc//hosts'
  expect_rc 0
  end
}
begin cli-core-edit-parent-components && {
  cli_core_grant_bob
  run bob 'SUDO_EDITOR=/usr/bin/true sudoedit -n /etc/../etc/hosts'
  expect_rc 0
  end
}
begin cli-core-edit-raw-policy-operands && {
  printf 'bob ALL=(root) NOPASSWD: sudoedit ./hosts\n' > /etc/sudoers.d/40-cli
  chmod 0440 /etc/sudoers.d/40-cli
  run bob 'cd /etc && SUDO_EDITOR=/usr/bin/true sudoedit -n ./hosts'
  expect_rc 0
  end
}
begin cli-core-edit-safe-writable-ancestor && {
  cli_core_grant_bob
  mkdir -p /tmp/cli-edit-safe
  chmod 0755 /tmp/cli-edit-safe
  printf 'original\n' > /tmp/cli-edit-safe/file
  run bob 'SUDO_EDITOR=/usr/bin/true sudoedit -n /tmp/cli-edit-safe/file'
  expect_rc 0
  end
}
begin cli-core-edit-follow && {
  printf 'bob ALL=(root) NOPASSWD: FOLLOW: sudoedit /etc/cli-edit-link\n' > /etc/sudoers.d/40-cli
  chmod 0440 /etc/sudoers.d/40-cli
  ln -sf /etc/hosts /etc/cli-edit-link
  run bob 'SUDO_EDITOR=/usr/bin/true sudoedit -n /etc/cli-edit-link'
  expect_rc 0
  end
}
begin cli-core-edit-checkdir-disabled && {
  cli_core_grant_bob
  printf 'Defaults:bob !sudoedit_checkdir\n' >> /etc/sudoers.d/40-cli
  printf 'original\n' > /home/bob/cli-edit-file
  run bob 'SUDO_EDITOR=/usr/bin/true sudoedit -n /home/bob/cli-edit-file'
  expect_rc 0
  end
}

begin cli-core-residual-denial-fqdn && {
  cp /etc/hosts "$WORK/cli-hosts"
  { printf '127.0.1.1 %s.example.test %s\n' "$host" "$host"; cat "$WORK/cli-hosts"; } > /etc/hosts
  run carol 'printf "carolpw\n" | sudo -kS /usr/bin/cat /etc/hostname'
  expect_rc 1
  expect_err_has "as root on $host.example.test."
  cat "$WORK/cli-hosts" > /etc/hosts
  end
}
begin cli-core-residual-denial-message && {
  printf 'Defaults:carol cmddenial_message="Ask IT"\n' > /etc/sudoers.d/40-cli
  chmod 0440 /etc/sudoers.d/40-cli
  run carol 'printf "carolpw\n" | sudo -kS /usr/bin/cat /etc/hostname'
  expect_rc 1
  [[ $ERR == *"as root on $host."$'\nAsk IT' ]] || fail "custom denial must follow the Sorry line"
  end
}
begin cli-core-residual-authfail-message && {
  printf '%s\n' 'Defaults:alice authfail_message="%d bad %% %x %", logfile="/tmp/cli-auth-failure"' > /etc/sudoers.d/40-cli
  chmod 0440 /etc/sudoers.d/40-cli
  rm -f /tmp/cli-auth-failure
  run alice 'printf "bad\nbad\nbad\n" | sudo -kS /usr/bin/true'
  expect_rc 1
  expect_err_has '3 bad % %x %'
  [[ $(cat /tmp/cli-auth-failure) == *"3 bad % %x % ;"* ]] || fail "auth failure log must expand configured message"
  end
}
begin cli-core-residual-exempt-password && {
  printf 'Defaults exempt_group=sudo\n' > /etc/sudoers.d/40-cli
  chmod 0440 /etc/sudoers.d/40-cli
  run alice 'sudo -nk /usr/bin/true'
  expect_rc 0
  end
}
begin cli-core-residual-exempt-path && {
  printf 'Defaults exempt_group=sudo\n' > /etc/sudoers.d/40-cli
  chmod 0440 /etc/sudoers.d/40-cli
  mkdir -p /home/alice/bin
  printf '#!/bin/sh\nprintf "exempt\\n%%s\\n" "$PATH"\n' > /home/alice/bin/cli-exempt-check
  chmod 0755 /home/alice/bin/cli-exempt-check
  run alice 'PATH=/home/alice/bin:/usr/bin:/bin sudo -nk cli-exempt-check'
  expect_rc 0
  expect_out_line exempt
  expect_out_line /home/alice/bin:/usr/bin:/bin
  end
}
begin cli-core-residual-runas-shell-invalid && {
  printf 'Defaults runas_check_shell\n' > /etc/sudoers.d/40-cli
  chmod 0440 /etc/sudoers.d/40-cli
  run root 'sudo -n -u nobody /usr/bin/true'
  expect_rc 1
  expect_err_has 'invalid shell for user nobody:'
  end
}
begin cli-core-residual-runas-shell-valid && {
  printf 'Defaults runas_check_shell\n' > /etc/sudoers.d/40-cli
  chmod 0440 /etc/sudoers.d/40-cli
  run root 'sudo -n -u bob /usr/bin/id -un'
  expect_rc 0
  expect_out_line bob
  end
}
begin cli-core-residual-runas-unknown-id && {
  printf 'Defaults runas_allow_unknown_id\n' > /etc/sudoers.d/40-cli
  chmod 0440 /etc/sudoers.d/40-cli
  run root "sudo -n -u '#54321' /usr/bin/id -u"
  expect_rc 0
  expect_out_line 54321
  end
}
begin cli-core-residual-runas-unknown-id-disabled && {
  run root "sudo -n -u '#54321' /usr/bin/id -u"
  expect_rc 1
  expect_err_has 'unknown user #54321'
  end
}
begin cli-core-residual-self-apparmor-auth && {
  printf 'ivan ALL=(ivan) APPARMOR_PROFILE=cli-test-profile /usr/bin/id\n' > /etc/sudoers.d/40-cli
  chmod 0440 /etc/sudoers.d/40-cli
  run ivan 'sudo -nk -u ivan /usr/bin/id'
  expect_rc 1
  expect_err_has 'a password is required'
  end
}
# Residual audit rows 21/22, sudo.ws v1.9.17p2:
# https://github.com/sudo-project/sudo/blob/v1.9.17p2/src/parse_args.c
# parse_env_list adds a name only when getenv succeeds; case 'R' warns after its
# empty/duplicate checks, before subsequent options and final validation.
# glibc posix/getopt.c emits scanner diagnostics using argv[0], not getprogname().
cli_second_compare_reference() {
  local user=$1 args=$2 status=$3
  # Preserve the exact argv[0] across implementations, without rewriting output.
  run "$user" '/bin/bash -c '\''exec -a /usr/bin/sudo /usr/bin/sudo.ws "$@"'\'' -- '"$args"
  expect_rc "$status"
  cp "$WORK/out" "$WORK/cli-second-reference-out"
  cp "$WORK/err" "$WORK/cli-second-reference-err"
  run "$user" "/usr/bin/sudo $args"
  expect_rc "$status"
  diff -u "$WORK/cli-second-reference-out" "$WORK/out" >>"$LOG" || fail 'stdout differs from sudo.ws'
  diff -u "$WORK/cli-second-reference-err" "$WORK/err" >>"$LOG" || fail 'stderr differs from sudo.ws'
}

begin cli-core-second-cli-timeout-plugin-error && {
  cli_second_compare_reference bob '-T nonsense true' 1
  end
}
begin cli-core-second-cli-timeout-empty-plugin-error && {
  cli_second_compare_reference bob "-T '' true" 1
  end
}
begin cli-core-second-cli-timeout-getopt-order && {
  cli_second_compare_reference bob '-T nonsense -z' 1
  end
}
begin cli-core-second-cli-timeout-version-order && {
  cli_second_compare_reference bob '-T nonsense -V' 1
  end
}
begin cli-core-second-cli-timeout-root-version-order && {
  cli_second_compare_reference root '-T nonsense -V' 1
  end
}

begin cli-core-second-cli-getopt-full-argv0 && {
  cli_second_compare_reference bob '-z' 1
  expect_out_empty
  [[ $ERR == "/usr/bin/sudo: invalid option -- 'z'"$'\nusage: sudo '* ]] || fail 'getopt error must retain full argv[0], followed by sudo usage'
  end
}
begin cli-core-second-cli-ordinary-program-identity && {
  cli_second_compare_reference bob '-i -s' 1
  expect_out_empty
  [[ $ERR == 'sudo: you may not specify both the -i and -s options'$'\nusage: sudo '* ]] || fail 'ordinary error must use sudo identity, not the executable path'
  end
}
begin cli-core-second-cli-chroot-version-order && {
  cli_second_compare_reference bob '-R / -V 2>&1' 0
  [[ $OUT == 'sudo: the -R option will be removed in a future version of sudo'$'\nSudo version 1.9.17p2\n'* ]] || fail 'chroot warning must precede version stdout'
  [[ -z $ERR ]] || fail 'combined output unexpectedly left stderr'
  end
}
begin cli-core-second-cli-chroot-usage-order && {
  cli_second_compare_reference bob '-R / -i -s' 1
  expect_out_empty
  [[ $ERR == 'sudo: the -R option will be removed in a future version of sudo'$'\nsudo: you may not specify both the -i and -s options\nusage: sudo '* ]] || fail 'chroot warning must precede validation error and usage'
  end
}
begin cli-core-second-cli-chroot-getopt-order && {
  cli_second_compare_reference bob '-R / -z' 1
  expect_out_empty
  [[ $ERR == 'sudo: the -R option will be removed in a future version of sudo'$'\n'"/usr/bin/sudo: invalid option -- 'z'"$'\nusage: sudo '* ]] || fail 'chroot warning must survive a later getopt error'
  end
}
begin cli-core-second-cli-chroot-duplicate-warning && {
  cli_second_compare_reference bob '-R / -R /' 1
  [[ $ERR == 'sudo: the -R option will be removed in a future version of sudo'$'\nusage: sudo '* ]] || fail 'duplicate chroot must not emit a second warning'
  end
}
begin cli-core-second-cli-chroot-not-reached && {
  cli_second_compare_reference bob '-z -R /' 1
  expect_err_lacks 'the -R option will be removed'
  end
}
begin cli-core-second-cli-edit-preserve-unset && {
  cli_core_grant_bob
  printf 'original\n' >/etc/cli-second-edit
  chmod 0644 /etc/cli-second-edit
  XENV=(SUDO_EDITOR=/bin/true)
  cli_second_compare_reference bob '-n -e --preserve-env=CLI_SECOND_UNSET /etc/cli-second-edit' 0
  expect_err_lacks 'you may not specify environment variables in edit mode'
  [[ $(cat /etc/cli-second-edit) == original ]] || fail 'no-op editor changed original'
  rm -f /etc/cli-second-edit
  end
}
begin cli-core-second-cli-edit-preserve-set && {
  XENV=(CLI_SECOND_SET=value)
  cli_second_compare_reference bob '-e --preserve-env=CLI_SECOND_SET /etc/hosts' 1
  [[ $ERR == 'sudo: you may not specify environment variables in edit mode'$'\nusage: sudo '* ]] || fail 'set preserve-list variable must fail before policy lookup'
  end
}
begin cli-core-second-cli-edit-preserve-set-empty && {
  XENV=(CLI_SECOND_SET=)
  cli_second_compare_reference bob '--preserve-env=CLI_SECOND_UNSET,CLI_SECOND_SET -e /etc/hosts' 1
  [[ $ERR == 'sudo: you may not specify environment variables in edit mode'$'\nusage: sudo '* ]] || fail 'empty value is set and must be rejected in edit mode'
  end
}
# Second residual environment audit: sudo.ws v1.9.17p2 env.c/env_pattern.c.
begin cli-core-second-env-explicit-path && {
  cli_core_grant_bob
  printf 'Defaults secure_path="/usr/bin:/bin"\n' > /etc/sudoers.d/40-cli
  chmod 0440 /etc/sudoers.d/40-cli
  run bob 'sudo -n PATH=/explicit/path /usr/bin/printenv PATH'
  expect_rc 0
  expect_out_line '/explicit/path'
  end
}
begin cli-core-second-env-preserve-path && {
  cli_core_grant_bob
  printf 'Defaults secure_path="/usr/bin:/bin"\n' > /etc/sudoers.d/40-cli
  chmod 0440 /etc/sudoers.d/40-cli
  run bob 'PATH=/preserved/path:/usr/bin sudo -n --preserve-env=PATH /usr/bin/printenv PATH'
  expect_rc 0
  expect_out_line '/preserved/path:/usr/bin'
  end
}
begin cli-core-second-env-explicit-identity && {
  cli_core_grant_bob
  run bob 'sudo -n SUDO_USER=explicit SUDO_UID=42 SUDO_GID=43 SUDO_COMMAND=changed /usr/bin/env'
  expect_rc 0
  expect_out_line 'SUDO_USER=explicit'
  expect_out_line 'SUDO_UID=42'
  expect_out_line 'SUDO_GID=43'
  expect_out_line 'SUDO_COMMAND=changed'
  end
}
begin cli-core-second-env-preserve-identity && {
  cli_core_grant_bob
  run bob 'SUDO_USER=preserved sudo -n --preserve-env=SUDO_USER /usr/bin/printenv SUDO_USER'
  expect_rc 0
  expect_out_line 'preserved'
  end
}
begin cli-core-second-env-path-validation && {
  printf 'Defaults secure_path="/usr/bin:/bin"\nbob ALL=(ALL:ALL) NOPASSWD: NOSETENV: ALL\n' > /etc/sudoers.d/40-cli
  chmod 0440 /etc/sudoers.d/40-cli
  run bob 'sudo -n PATH=/forbidden /usr/bin/printenv PATH'
  expect_rc 1
  expect_err_has 'you are not allowed to set the following environment variables: PATH'
  end
}
begin cli-core-second-env-identity-whitelisted && {
  printf 'Defaults env_keep += "SUDO_USER"\nbob ALL=(ALL:ALL) NOPASSWD: NOSETENV: ALL\n' > /etc/sudoers.d/40-cli
  chmod 0440 /etc/sudoers.d/40-cli
  run bob 'sudo -n SUDO_USER=approved /usr/bin/printenv SUDO_USER'
  expect_rc 0
  expect_out_line 'approved'
  end
}
begin cli-core-second-env-internal-stars && {
  cli_core_grant_bob
  printf 'Defaults env_keep += "*_PROXY XDG_*_DIR"\n' > /etc/sudoers.d/40-cli
  chmod 0440 /etc/sudoers.d/40-cli
  run bob 'HTTP_PROXY=proxy XDG_CACHE_DIR=/site/cache sudo -n /usr/bin/env'
  expect_rc 0
  expect_out_line 'HTTP_PROXY=proxy'
  expect_out_line 'XDG_CACHE_DIR=/site/cache'
  end
}
begin cli-core-second-env-value-pattern && {
  cli_core_grant_bob
  printf 'Defaults env_keep += "SITE_ALLOWED=trusted* SITE_DENIED=trusted*"\n' > /etc/sudoers.d/40-cli
  chmod 0440 /etc/sudoers.d/40-cli
  run bob 'SITE_ALLOWED=trusted-value SITE_DENIED=other sudo -n /usr/bin/env'
  expect_rc 0
  expect_out_line 'SITE_ALLOWED=trusted-value'
  expect_out_lacks 'SITE_DENIED='
  end
}
begin cli-core-second-env-value-check && {
  cli_core_grant_bob
  printf 'Defaults env_check += "SITE_SAFE=ok* SITE_UNSAFE=ok*"\n' > /etc/sudoers.d/40-cli
  chmod 0440 /etc/sudoers.d/40-cli
  run bob 'SITE_SAFE=okay SITE_UNSAFE=ok/unsafe sudo -n /usr/bin/env'
  expect_rc 0
  expect_out_line 'SITE_SAFE=okay'
  expect_out_lacks 'SITE_UNSAFE='
  end
}
begin cli-core-second-env-value-delete && {
  cli_core_grant_bob
  printf 'Defaults !env_reset\nDefaults env_delete += "SITE_BAD=bad* SITE_GOOD=bad*"\n' > /etc/sudoers.d/40-cli
  chmod 0440 /etc/sudoers.d/40-cli
  run bob 'SITE_BAD=bad-value SITE_GOOD=good-value sudo -n /usr/bin/env'
  expect_rc 0
  expect_out_lacks 'SITE_BAD='
  expect_out_line 'SITE_GOOD=good-value'
  end
}
begin cli-core-second-env-logname-user-coupling && {
  cli_core_grant_bob
  printf 'Defaults env_keep += "LOGNAME"\n' > /etc/sudoers.d/40-cli
  chmod 0440 /etc/sudoers.d/40-cli
  run bob 'LOGNAME=login-value USER=user-value sudo -n /usr/bin/env'
  expect_rc 0
  expect_out_line 'LOGNAME=login-value'
  expect_out_line 'USER=user-value'
  end
}
begin cli-core-second-env-identity-value-pattern && {
  cli_core_grant_bob
  printf 'Defaults env_keep += "USER=user-value LOGNAME=login-value"\n' > /etc/sudoers.d/40-cli
  chmod 0440 /etc/sudoers.d/40-cli
  run bob 'LOGNAME=login-value USER=user-value sudo -n /usr/bin/env'
  expect_rc 0
  expect_out_line 'LOGNAME=root'
  expect_out_line 'USER=root'
  end
}
begin cli-core-second-env-function-value-qualified && {
  cli_core_grant_bob
  printf 'Defaults env_keep += "SITE_FN=()*"\n' > /etc/sudoers.d/40-cli
  chmod 0440 /etc/sudoers.d/40-cli
  run bob "SITE_FN='() { :; }' sudo -n /usr/bin/printenv SITE_FN"
  expect_rc 0
  expect_out_line '() { :; }'
  end
}
begin cli-core-second-env-function-name-only && {
  cli_core_grant_bob
  printf 'Defaults env_keep += "SITE_FN"\n' > /etc/sudoers.d/40-cli
  chmod 0440 /etc/sudoers.d/40-cli
  run bob "SITE_FN='() { :; }' sudo -n /usr/bin/printenv SITE_FN"
  expect_rc 1
  end
}
begin cli-core-second-env-function-setenv && {
  cli_core_grant_bob
  run bob "sudo -n SITE_FN='() { :; }' /usr/bin/printenv SITE_FN"
  expect_rc 0
  expect_out_line '() { :; }'
  end
}
begin cli-core-second-env-pam-trusted && {
  cli_core_grant_bob
  cp -a /etc/environment "$WORK/cli-core-second-env-environment"
  printf '\nPYTHONPATH=/opt/trusted-python\nSITE_PAM=trusted\n' >> /etc/environment
  run bob 'sudo -n /usr/bin/env'
  expect_rc 0
  expect_out_line 'PYTHONPATH=/opt/trusted-python'
  expect_out_line 'SITE_PAM=trusted'
  cp -a "$WORK/cli-core-second-env-environment" /etc/environment
  end
}
begin cli-core-second-env-pam-overwrite-explicit && {
  cli_core_grant_bob
  cp -a /etc/environment "$WORK/cli-core-second-env-environment"
  printf '\nSUDO_USER=pam-user\n' >> /etc/environment
  run bob 'sudo -n SUDO_USER=explicit /usr/bin/printenv SUDO_USER'
  expect_rc 0
  expect_out_line 'pam-user'
  cp -a "$WORK/cli-core-second-env-environment" /etc/environment
  end
}
begin cli-core-second-env-pam-kept-explicit && {
  cli_core_grant_bob
  printf 'Defaults env_keep += "SUDO_USER"\n' > /etc/sudoers.d/40-cli
  chmod 0440 /etc/sudoers.d/40-cli
  cp -a /etc/environment "$WORK/cli-core-second-env-environment"
  printf '\nSUDO_USER=pam-user\n' >> /etc/environment
  run bob 'sudo -n SUDO_USER=explicit /usr/bin/printenv SUDO_USER'
  expect_rc 0
  expect_out_line 'explicit'
  cp -a "$WORK/cli-core-second-env-environment" /etc/environment
  end
}
begin cli-core-second-env-pam-check-incoming-value && {
  cli_core_grant_bob
  printf 'Defaults env_check += "SITE_CHECK"\n' > /etc/sudoers.d/40-cli
  chmod 0440 /etc/sudoers.d/40-cli
  cp -a /etc/environment "$WORK/cli-core-second-env-environment"
  printf '\nSITE_CHECK=unsafe/value\n' >> /etc/environment
  run bob 'SITE_CHECK=safe sudo -n /usr/bin/printenv SITE_CHECK'
  expect_rc 0
  expect_out_line 'unsafe/value'
  cp -a "$WORK/cli-core-second-env-environment" /etc/environment
  end
}
begin cli-core-second-env-pam-copy-mode && {
  cli_core_grant_bob
  printf 'Defaults !env_reset\n' > /etc/sudoers.d/40-cli
  chmod 0440 /etc/sudoers.d/40-cli
  cp -a /etc/environment "$WORK/cli-core-second-env-environment"
  printf '\nPYTHONPATH=/pam/python\nSITE_KEEP=pam\n' >> /etc/environment
  run bob 'SITE_KEEP=user sudo -n PYTHONPATH=/explicit/python /usr/bin/env'
  expect_rc 0
  expect_out_line 'PYTHONPATH=/pam/python'
  expect_out_line 'SITE_KEEP=user'
  cp -a "$WORK/cli-core-second-env-environment" /etc/environment
  end
}
begin cli-core-second-env-preserve-before-assignment && {
  cli_core_grant_bob
  run bob 'SITE_ORDER=preserved sudo -n --preserve-env=SITE_ORDER SITE_ORDER=explicit /usr/bin/printenv SITE_ORDER'
  expect_rc 0
  expect_out_line 'explicit'
  end
}
begin cli-core-second-env-preserve-after-assignment && {
  cli_core_grant_bob
  run bob 'SITE_ORDER=preserved sudo -n SITE_ORDER=explicit --preserve-env=SITE_ORDER /usr/bin/printenv SITE_ORDER'
  expect_rc 0
  expect_out_line 'preserved'
  end
}
begin cli-core-second-env-repeated-preserve && {
  cli_core_grant_bob
  run bob 'SITE_ORDER=preserved sudo -n --preserve-env=SITE_ORDER SITE_ORDER=explicit --preserve-env=SITE_ORDER /usr/bin/printenv SITE_ORDER'
  expect_rc 0
  expect_out_line 'preserved'
  end
}
begin cli-core-second-env-preserve-all-and-list && {
  cli_core_grant_bob
  printf 'Defaults secure_path="/usr/bin:/bin"\n' > /etc/sudoers.d/40-cli
  chmod 0440 /etc/sudoers.d/40-cli
  run bob 'PATH=/preserved:/usr/bin sudo -n -E --preserve-env=PATH /usr/bin/printenv PATH'
  expect_rc 0
  expect_out_line '/preserved:/usr/bin'
  end
}

begin cli-core-second-core-list-short-host && {
  cp /etc/hosts "$WORK/cli-second-hosts"
  { printf '127.0.1.1 %s.example.test %s\n' "$host" "$host"; cat "$WORK/cli-second-hosts"; } > /etc/hosts
  cli_second_compare_reference root '-n -l -U alice' 0
  expect_out_has "User alice may run the following commands on $host:"
  cat "$WORK/cli-second-hosts" > /etc/hosts
  end
}
begin cli-core-second-core-nohost-short-host && {
  cp /etc/hosts "$WORK/cli-second-hosts"
  { printf '127.0.1.1 %s.example.test %s\n' "$host" "$host"; cat "$WORK/cli-second-hosts"; } > /etc/hosts
  printf 'ivan remote = /usr/bin/true\n' > /etc/sudoers.d/40-cli
  chmod 0440 /etc/sudoers.d/40-cli
  run ivan 'printf "ivanpw\n" | sudo -kS /usr/bin/true'
  expect_rc 1
  expect_err_has "ivan is not allowed to run sudo on $host."
  expect_err_lacks "$host.example.test"
  cat "$WORK/cli-second-hosts" > /etc/hosts
  end
}
begin cli-core-second-core-list-denial && {
  printf 'Defaults:bob logfile="/tmp/cli-second-list-log"\n' > /etc/sudoers.d/40-cli
  chmod 0440 /etc/sudoers.d/40-cli
  rm -f /tmp/cli-second-list-log
  run bob 'printf "bobpw\n" | sudo -kS -l'
  expect_rc 1
  expect_err_has "Sorry, user bob may not run sudo on $host."
  [[ $(cat /tmp/cli-second-list-log) == *"command not allowed ;"* ]] || fail 'listing denial reason differs'
  end
}
begin cli-core-second-core-validate-denial && {
  printf 'Defaults:bob logfile="/tmp/cli-second-validate-log"\n' > /etc/sudoers.d/40-cli
  chmod 0440 /etc/sudoers.d/40-cli
  rm -f /tmp/cli-second-validate-log
  run bob 'printf "bobpw\n" | sudo -kS -v'
  expect_rc 1
  expect_err_has "Sorry, user bob may not run sudo on $host."
  [[ $(cat /tmp/cli-second-validate-log) == *"command not allowed ;"* ]] || fail 'validation denial reason differs'
  end
}
begin cli-core-second-core-list-other-denial && {
  printf 'Defaults:ivan logfile="/tmp/cli-second-other-log"\nivan ALL=(ivan) /usr/bin/true\n' > /etc/sudoers.d/40-cli
  chmod 0440 /etc/sudoers.d/40-cli
  rm -f /tmp/cli-second-other-log
  run ivan 'printf "ivanpw\n" | sudo -kS -l -U kate'
  expect_rc 1
  expect_err_has "Sorry, user ivan is not allowed to execute 'list' as kate on $host."
  [[ $(cat /tmp/cli-second-other-log) == *"command not allowed ;"* ]] || fail 'other-user listing denial must be logged'
  end
}
begin cli-core-second-core-list-other-auth-first && {
  printf 'ivan ALL=(ivan) /usr/bin/true\n' > /etc/sudoers.d/40-cli
  chmod 0440 /etc/sudoers.d/40-cli
  run ivan 'sudo -nk -l -U kate'
  expect_rc 1
  expect_err_has 'a password is required'
  expect_err_lacks 'is not allowed to execute'
  end
}
begin cli-core-second-core-list-rootpw && {
  printf 'Defaults:alice rootpw\n' > /etc/sudoers.d/40-cli
  chmod 0440 /etc/sudoers.d/40-cli
  run alice 'printf "alicepw\n" | sudo -kS -l'
  expect_rc 0
  expect_out_has 'User alice may run the following commands'
  end
}
begin cli-core-second-core-list-targetpw && {
  printf 'Defaults:alice targetpw\n' > /etc/sudoers.d/40-cli
  chmod 0440 /etc/sudoers.d/40-cli
  run alice 'printf "alicepw\n" | sudo -kS -l'
  expect_rc 0
  end
}
begin cli-core-second-core-list-runaspw && {
  printf 'Defaults:alice runaspw\n' > /etc/sudoers.d/40-cli
  chmod 0440 /etc/sudoers.d/40-cli
  run alice 'printf "alicepw\n" | sudo -kS -l'
  expect_rc 0
  end
}
begin cli-core-second-core-runaspw-other-target && {
  printf 'Defaults:alice runaspw, runas_default=carol\n' > /etc/sudoers.d/40-cli
  chmod 0440 /etc/sudoers.d/40-cli
  run alice 'printf "carolpw\n" | sudo -kS -u bob /usr/bin/id -un'
  expect_rc 0
  expect_out_line bob
  end
}
begin cli-core-second-core-login-cwd && {
  printf 'root ALL=(ALL:ALL) CWD=/tmp NOPASSWD: ALL\n' > /etc/sudoers.d/40-cli
  chmod 0440 /etc/sudoers.d/40-cli
  run root 'sudo -ni /usr/bin/pwd'
  expect_rc 0
  expect_out_line /tmp
  end
}
begin cli-core-second-core-login-runcwd && {
  printf 'Defaults runcwd="/tmp"\n' > /etc/sudoers.d/40-cli
  chmod 0440 /etc/sudoers.d/40-cli
  run root 'sudo -ni /usr/bin/pwd'
  expect_rc 0
  expect_out_line /tmp
  end
}
begin cli-core-second-core-login-chdir && {
  printf 'Defaults runcwd="*"\n' > /etc/sudoers.d/40-cli
  chmod 0440 /etc/sudoers.d/40-cli
  run root 'sudo -ni -D /tmp /usr/bin/pwd'
  expect_rc 0
  expect_out_line /tmp
  end
}
begin cli-core-second-core-login-missing-required-cwd && {
  printf 'Defaults runcwd="/cli-second-missing-directory"\n' > /etc/sudoers.d/40-cli
  chmod 0440 /etc/sudoers.d/40-cli
  run root 'sudo -ni /usr/bin/true'
  expect_rc 1
  expect_err_has 'unable to change directory to /cli-second-missing-directory'
  end
}
