#!/bin/bash

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





cli_second_compare_reference() {
  local user=$1 args=$2 status=$3

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




cli_core_third_event_fixture() {
  cat >"$WORK/cli-core-third-event.py" <<'PY'
import json, os, pathlib, pwd, re, shutil, socket, subprocess, sys, tempfile, time

class Pairs(list):
    pass

def decode(text):
    return json.loads(text, object_pairs_hook=Pairs)

def normalize_json(value, key=''):
    if isinstance(value, Pairs):
        return Pairs((k, normalize_json(v, k)) for k, v in value)
    if isinstance(value, list):
        return [normalize_json(v) for v in value]
    if key in ('seconds', 'nanoseconds'):
        assert isinstance(value, int) and value >= 0, (key, value)
        if key == 'nanoseconds': assert value < 1000000000, value
        return '<time>'
    if key == 'iso8601':
        assert re.fullmatch(r'\d{14}Z', value), value
        return '<utc>'
    if key == 'localtime':
        assert re.fullmatch(r'[A-Z][a-z]{2} [ 0-9][0-9] \d\d:\d\d:\d\d', value), value
        return '<local>'
    return value

def normalize_identity(value, identity):


    if isinstance(value, Pairs):
        result = Pairs()
        for key, item in value:
            if key == 'uuid':
                assert item == identity, (item, identity)
                result.append((key, '<invocation-uuid>'))
            else:
                result.append((key, normalize_identity(item, identity)))
        return result
    if isinstance(value, dict):
        return {k: normalize_identity(v, identity) for k, v in value.items()}
    if isinstance(value, (list, tuple)):
        return type(value)(normalize_identity(v, identity) for v in value)
    return value

def normalize_log(text, fmt):
    if not text: return [] if fmt != 'sudo' else ''
    if fmt == 'json_compact':
        return [normalize_json(decode(line)) for line in text.splitlines()]
    if fmt != 'sudo': return normalize_json(decode(text))
    return re.sub(r'(?m)^[A-Z][a-z]{2} [ 0-9][0-9] \d\d:\d\d:\d\d : ', '<time> : ', text)

def normalize_syslog(message):

    match = re.fullmatch(r'(<\d+>)[A-Z][a-z]{2} [ 0-9][0-9] \d\d:\d\d:\d\d (sudo)(?:\[\d+\])?: (.*)', message, re.S)
    assert match, ('unexpected syslog transport', message)
    prefix = match[1] + '<time> ' + match[2] + '[<pid>]: '
    if match[3].startswith('@cee:'):
        return (prefix, normalize_json(decode(match[3][5:])))
    return prefix + match[3]

def execute(binary, args, user='judy', cwd=None, env=None,
            logfile='/tmp/cli-core-third-event.log', fmt='sudo'):
    account = pwd.getpwnam(user)
    if cwd is None: cwd = account.pw_dir
    if env is None:
        env = dict(HOME=account.pw_dir, USER=user, LOGNAME=user, SHELL='/bin/bash',
                   PATH='/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin', LANG='C.UTF-8')
    path = pathlib.Path(logfile)
    path.unlink(missing_ok=True)
    import sys
    sys.path.insert(0, '/usr/local/lib')
    from sudo_it_logging import Syslog
    with Syslog() as logger:
        result = subprocess.run(['setpriv', '--reuid=' + str(account.pw_uid),
            '--regid=' + str(account.pw_gid), '--init-groups', '--',
            '/bin/bash', '-c', 'exec -a sudo "$@"', 'sh', binary, *args],
            cwd=cwd, env=env, stdin=subprocess.DEVNULL, capture_output=True,
            start_new_session=True, timeout=20)
        messages = logger.messages()
    return dict(rc=result.returncode, out=result.stdout, err=result.stderr,
        logfile=normalize_log(path.read_text() if path.exists() else '', fmt),
        syslog=[normalize_syslog(message) for message in messages])

def event_case(fmt, scenario):
    with tempfile.TemporaryDirectory(prefix='cli-core-third-event-', dir='/tmp') as tmp:
        root = pathlib.Path(tmp)
        root.chmod(0o755)
        logfile = root / 'events.log'
        mail = pathlib.Path('/var/mail/root')
        mailer = pathlib.Path('/usr/sbin/sendmail')
        args = ['-n', '/usr/bin/true']
        user = 'judy'
        options = []
        tags = 'NOSETENV:'
        kind = 'alert'
        reason = ''
        if scenario == 'notfound':
            args = ['-n', 'cli_core_third_event_missing']
            kind = None
        elif scenario == 'dot':
            command = root / 'cli_core_third_event_dot'
            command.write_text('#!/bin/sh\nexit 0\n')
            command.chmod(0o755)
            args = ['-n', command.name]
            options += ['ignore_dot', 'secure_path=\"/usr/bin:/bin:.\"']
            kind = None
        elif scenario == 'preserve':
            args = ['-n', '-E', '/usr/bin/true']
            reason = 'user not allowed to preserve the environment'
        elif scenario == 'variable':
            args = ['-n', 'LD_PRELOAD=cli-core-forbidden', '/usr/bin/true']
            reason = 'sorry, you are not allowed to set the following environment variables: LD_PRELOAD'
        elif scenario == 'timeout':
            args = ['-n', '-T', '5', '/usr/bin/true']
            reason = 'user not allowed to set a command timeout'
        elif scenario in ('cwd', 'chroot'):
            args = ['-n', '-D' if scenario == 'cwd' else '-R', '/tmp', '/usr/bin/true']
            reason = 'user not allowed to change ' + ('directory' if scenario == 'cwd' else 'root directory') + ' to /tmp'
        elif scenario.startswith('setid-'):
            command = root / 'setid'
            shutil.copyfile('/usr/bin/id', command)
            command.chmod(0o4755)
            args = ['-n', str(command), '-u']
            options += ['intercept_type=' + scenario[6:], '!intercept_allow_setid']
            tags += ' INTERCEPT:'
            kind = 'reject'
            reason = 'setid command rejected in intercept mode'
        elif scenario == 'remote-host':
            args = ['-n', '-h', 'localhost', '/usr/bin/true']
            reason = 'user not allowed to set remote host for command'
        elif scenario == 'closefrom':
            args = ['-n', '-C', '5', '/usr/bin/true']
            reason = 'user not allowed to override closefrom limit'
        elif scenario in ('unknown-uid', 'unknown-gid'):
            args = ['-n', '-u' if scenario == 'unknown-uid' else '-g', '#54321', '/usr/bin/true']
            options += ['!runas_allow_unknown_id']
            reason = 'unknown ' + ('user' if scenario == 'unknown-uid' else 'group') + ' #54321'
        elif scenario == 'impliedshell':
            args = ['-n']
            options += ['!shell_noargs']
            kind = None
        elif scenario == 'root-sudo':
            user = 'root'
            options += ['!root_sudo']
            kind = None
        elif scenario == 'requiretty':
            options += ['requiretty']
            reason = 'no tty'
        elif scenario == 'invalidshell':
            args = ['-n', '-u', 'nobody', '/usr/bin/true']
            options += ['runas_check_shell']
            reason = 'invalid shell for user nobody: /usr/sbin/nologin'
        else: raise AssertionError(scenario)


        if kind != 'reject': options += ['mail_always', 'mail_all_cmnds']
        config = root / 'server.conf'
        remote = root / 'remote.json'
        listener = socket.socket()
        listener.bind(('127.0.0.1', 0))
        port = listener.getsockname()[1]
        listener.close()
        config.write_text('[server]\nlisten_address = 127.0.0.1:' + str(port) +
            '\npid_file = ' + str(root / 'pid') + '\nserver_log = ' + str(root / 'server.log') +
            '\ntimeout = 2\n[eventlog]\nlog_type = logfile\nlog_format = json\n[logfile]\npath = ' + str(remote) + '\n')
        policy = pathlib.Path('/etc/sudoers.d/zz-cli-core-third-event')
        policy.write_text('Defaults !authenticate, !use_pty, !requiretty, !log_exit_status, log_allowed, log_denied, loglinelen=0, syslog_maxlen=9600, syslog=authpriv, syslog_goodpri=notice, syslog_badpri=alert, logfile="' + str(logfile) + '", log_format=' + fmt + ', mailerpath="' + str(mailer) + '", mailerflags="-t", mailto="root", log_servers="127.0.0.1:' + str(port) + '", log_server_timeout=2' +
            (', ' + ', '.join(options) if options else '') + '\n' +
            user + ' ALL=(ALL:ALL) NOPASSWD: ' + tags + ' ALL\n')
        policy.chmod(0o440)
        def observed(binary):
            remote.unlink(missing_ok=True)
            mail.unlink(missing_ok=True)
            with (root / 'daemon.out').open('wb') as output:
                daemon = subprocess.Popen(['/usr/sbin/sudo_logsrvd', '-n', '-f', str(config)], stdout=output, stderr=output)
                try:
                    for attempt in range(100):
                        assert daemon.poll() is None, (root / 'daemon.out').read_text()
                        try:
                            with socket.create_connection(('127.0.0.1', port), .05): pass
                            break
                        except OSError: time.sleep(.02)
                    else: raise AssertionError('sudo_logsrvd did not listen')
                    result = execute(binary, args, user=user, cwd=str(root), logfile=logfile, fmt=fmt)


                    deadline = time.monotonic() + 1
                    while time.monotonic() < deadline:
                        if kind != 'reject':
                            assert not mail.exists() or not mail.stat().st_size, (binary, mail.read_text())
                        time.sleep(.01)
                    if kind:
                        deadline = time.monotonic() + 5
                        while not (remote.exists() and remote.stat().st_size):
                            assert time.monotonic() < deadline, 'remote event did not arrive'
                            time.sleep(.01)
                finally:
                    daemon.terminate()
                    daemon.wait(timeout=5)
            remote_events = decode(remote.read_text()) if remote.exists() and remote.stat().st_size else Pairs()
            remote_kinds = [k for k, _ in remote_events]
            assert 'accept' not in remote_kinds, (binary, remote_events)
            assert remote_kinds == ([kind] if kind else []), (binary, remote_events)
            if kind:
                assert dict(remote_events[0][1])['reason'] == reason, remote_events
            if kind != 'reject': assert not mail.exists() or not mail.stat().st_size, (binary, mail.read_text())
            assert result['rc'] == 1 and result['out'] == b'', (binary, result)
            if scenario == 'notfound': assert b'cli_core_third_event_missing: command not found' in result['err'], result
            if scenario == 'dot': assert b'ignoring \"cli_core_third_event_dot\" found in' in result['err'], result
            if kind is None:
                assert not result['logfile'] and not result['syslog'], (binary, result)
            else:
                assert len(result['syslog']) == 1, (binary, result)
                message = result['syslog'][0]
                assert (message[0] if isinstance(message, tuple) else message).startswith('<81>'), (binary, message)
                if fmt == 'sudo':
                    assert reason in result['logfile'] and reason in message, (binary, result)
                    if scenario == 'invalidshell':
                        assert result['logfile'] == '<time> : judy : ' + reason + '\n', result
                        assert message == '<81><time> sudo[<pid>]:     judy : ' + reason, result
                else:
                    records = result['logfile'][0] if fmt == 'json_compact' else result['logfile']
                    assert [k for k, _ in records] == [kind], records
                    fields = dict(records[0][1])
                    assert fields['reason'] == reason and 'alert_time' in fields, fields
                    if scenario in ('remote-host', 'closefrom'):
                        assert 'source' not in fields, fields
                    else:
                        assert fields['source'] == str(policy) + ':2:43', fields


                    assert message[1] == Pairs([('sudo', records)]), (message, records)
                    identity = fields['uuid']
                    assert re.fullmatch(r'[0-9a-f]{10}(?:-[0-9a-f]{4}){3}-[0-9a-f]{10}', identity), identity
                    result = normalize_identity(result, identity)
            print(binary, scenario, repr(result), 'remote=' + repr(remote_kinds), flush=True)
            return result
        reference = observed('/usr/bin/sudo.ws')
        actual = observed('/usr/bin/sudo')
        assert actual == reference, ('event mismatch', reference, actual)

if __name__ == '__main__':
    event_case(*sys.argv[1:])
PY
}

cli_core_third_event_compare() {
  cli_core_third_event_fixture
  python3 "$WORK/cli-core-third-event.py" "$1" "$2"
}

for cli_core_third_event_scenario in notfound dot preserve variable timeout cwd chroot setid-trace setid-dso remote-host closefrom unknown-uid unknown-gid impliedshell root-sudo requiretty invalidshell; do
  begin "cli-core-third-event-$cli_core_third_event_scenario" && {
    cli_core_third_event_compare sudo "$cli_core_third_event_scenario" >"$WORK/cli-core-third-event-result" 2>&1 || fail "$(cat "$WORK/cli-core-third-event-result")"
    cat "$WORK/cli-core-third-event-result" >>"$LOG"
    end
  }
done

for cli_core_third_event_format in json json_compact; do
  for cli_core_third_event_scenario in notfound preserve variable timeout cwd chroot remote-host closefrom unknown-uid unknown-gid impliedshell root-sudo requiretty invalidshell; do
    begin "cli-core-third-event-$cli_core_third_event_format-$cli_core_third_event_scenario" && {
      cli_core_third_event_compare "$cli_core_third_event_format" "$cli_core_third_event_scenario" >"$WORK/cli-core-third-event-result" 2>&1 || fail "$(cat "$WORK/cli-core-third-event-result")"
      cat "$WORK/cli-core-third-event-result" >>"$LOG"
      end
    }
  done
done




cli_core_third_order_compare() {
  cli_core_third_event_fixture
  python3 - "$WORK/cli-core-third-event.py" "$1" "$2" <<'PY'
import pathlib, pwd, runpy, shutil, sys

capture = runpy.run_path(sys.argv[1])['execute']
kind, scenario = sys.argv[2:]
logfile = '/tmp/cli-core-third-event.log'
policy = pathlib.Path('/etc/sudoers.d/zz-cli-third-order')
base = ('Defaults !authenticate, lecture=never, !use_pty, !log_exit_status, '
        'logfile="' + logfile + '", loglinelen=0, syslog=authpriv, '
        'syslog_goodpri=notice, syslog_badpri=alert, !mail_always, '
        '!mail_badpass, !mail_no_user, !mail_no_host, !mail_no_perms\n')
user, cwd, extra = 'ivan', None, {}
expected_rc, expected_error, expected_output = 1, None, None

def set_policy(settings='', rules='ivan ALL=(ALL:ALL) NOPASSWD: ALL\nroot ALL=(ALL:ALL) NOPASSWD: ALL\n'):
    policy.write_text(base + settings + rules)
    policy.chmod(0o440)

if kind == 'order':
    first, second = scenario.split('-')
    checks = {first, second}
    settings = 'Defaults !runas_allow_unknown_id\n'
    if 'root' in checks:
        user = 'root'
        settings += 'Defaults !root_sudo\n'
    if 'implied' in checks: settings += 'Defaults !shell_noargs\n'
    if 'tty' in checks: settings += 'Defaults requiretty\n'
    if 'shell' in checks:
        assert pwd.getpwnam('nobody').pw_shell not in pathlib.Path('/etc/shells').read_text().splitlines()
        settings += 'Defaults runas_check_shell\n'
    args = ['-n']
    if 'remote' in checks: args += ['-h', 'localhost']
    if 'close' in checks: args += ['-C', '5']
    if 'uid' in checks: args += ['-u', '#54321']
    elif 'shell' in checks: args += ['-u', 'nobody']
    if 'gid' in checks: args += ['-g', '#54321']
    if 'implied' not in checks: args += ['/usr/bin/true']
    set_policy(settings)
    expected_error = {
        'remote': 'a remote host may only be specified when listing privileges.',
        'root': 'sudoers specifies that root is not allowed to sudo',
        'close': 'you are not permitted to use the -C option',
        'uid': 'unknown user #54321',
        'gid': 'unknown group #54321',
        'implied': 'usage: sudo',
        'tty': 'sorry, you must have a tty to run sudo',
    }[first]
    expected_output = b''
elif kind == 'editcwd':
    tree = pathlib.Path('/srv/cli-third-editcwd')
    invoke, target, other = (tree / name for name in ('invoke', 'target', 'other'))
    for directory in (tree, invoke, target, other):
        directory.mkdir(parents=True, exist_ok=True)
        directory.chmod(0o755)
    for directory, text in ((invoke, 'invoking operand\n'), (target, 'target operand\n'), (other, 'other operand\n')):
        (directory / 'operand').write_text(text)
        (directory / 'operand').chmod(0o644)
    editor = tree / 'editor'
    editor.write_text('#!/bin/sh\nprintf "editor-pwd="; pwd\nfor file in "$@"; do\n'
                      '  [ "$file" = -- ] && continue\n'
                      '  printf "operand-content="; cat "$file"\ndone\n')
    editor.chmod(0o755)
    cwd = str(invoke)
    extra = {'SUDO_EDITOR': str(editor)}
    settings, rule = '', 'ivan ALL=(root) NOPASSWD: sudoedit\n'
    if scenario.startswith('wildcard'): settings = 'Defaults runcwd=*\n'
    if scenario.startswith('fixed'): settings = 'Defaults runcwd="' + str(target) + '"\n'

    if scenario.startswith('rule-wildcard'): rule = 'ivan ALL=(root) CWD=* NOPASSWD: sudoedit\n'
    if scenario == 'rule-fixed': rule = 'ivan ALL=(root) CWD=' + str(target) + ' NOPASSWD: sudoedit\n'
    set_policy(settings, rule)
    args = ['-n', '-e']
    if scenario not in ('fixed-default', 'rule-fixed'):
        args += ['-D', str(other if scenario == 'fixed-mismatch' else target)]
    relative = scenario.endswith('relative')
    args += ['operand' if relative else str(invoke / 'operand')]




    if scenario in ('forbidden', 'fixed-equal', 'fixed-mismatch'):
        expected_error = 'you are not permitted to use the -D option with sudoedit'
        expected_output = b''
    else:
        expected_rc = 0
        expected_output = ('editor-pwd=' + str(target) + '\noperand-content=invoking operand\n').encode()
        expected_error = 'unchanged'
elif kind == 'rootprivacy':
    tree = pathlib.Path('/srv/cli-third-rootprivacy')
    root = tree / 'root'
    tree.mkdir(parents=True, exist_ok=True)
    tree.chmod(0o755)
    if root.exists():
        root.chmod(0o755)
        shutil.rmtree(root)
    if scenario != 'missing':
        (root / 'usr/bin').mkdir(parents=True)
        shutil.copy2('/usr/bin/true', root / 'usr/bin/true')
        root.chmod(0 if scenario == 'unreadable' else 0o755)
    set_policy()
    args = ['-n', '-R', str(root), '/usr/bin/true']
    expected_error = 'you are not permitted to use the -R option with /usr/bin/true'
    expected_output = b''
else:
    raise AssertionError(kind)

account = pwd.getpwnam(user)
extra = dict(HOME=account.pw_dir, USER=user, LOGNAME=user, SHELL='/bin/bash',
             PATH='/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin',
             LANG='C.UTF-8', **extra)
reference = capture('/usr/bin/sudo.ws', args, user=user, cwd=cwd, env=extra, logfile=logfile)
print('reference:', repr(reference), flush=True)
assert reference['rc'] == expected_rc, reference
assert expected_error.encode() in reference['err'], reference
assert reference['out'] == expected_output, reference
if kind == 'rootprivacy':
    assert reference['err'] == (
        'sudo: the -R option will be removed in a future version of sudo\n'
        'sudo: ' + expected_error + '\n').encode(), reference
    assert len(reference['logfile'].splitlines()) == 1, reference
    assert len(reference['syslog']) == 1, reference
    assert 'user not allowed to change root directory to ' + str(root) in reference['logfile'], reference
    assert 'user not allowed to change root directory to ' + str(root) in reference['syslog'][0], reference
actual = capture('/usr/bin/sudo', args, user=user, cwd=cwd, env=extra, logfile=logfile)
print('actual:', repr(actual), flush=True)
assert actual == reference, 'stderr/stdout/status/logfile/syslog differ from sudo.ws'
if kind == 'editcwd':
    for directory, text in ((invoke, 'invoking operand\n'), (target, 'target operand\n'), (other, 'other operand\n')):
        assert (directory / 'operand').read_text() == text, directory
if kind == 'rootprivacy' and root.exists(): root.chmod(0o755)
PY
}

for cli_third_first in remote root close; do
  for cli_third_second in uid gid implied tty shell; do
    begin "cli-core-third-order-$cli_third_first-$cli_third_second" && {
      cli_core_third_order_compare order "$cli_third_first-$cli_third_second" >"$WORK/cli-third-order-result" 2>&1 || fail "$(cat "$WORK/cli-third-order-result")"
      cat "$WORK/cli-third-order-result" >>"$LOG"
      end
    }
  done
done
for cli_third_pair in remote-root remote-close root-close uid-tty gid-tty implied-tty tty-shell; do
  begin "cli-core-third-order-$cli_third_pair" && {
    cli_core_third_order_compare order "$cli_third_pair" >"$WORK/cli-third-order-result" 2>&1 || fail "$(cat "$WORK/cli-third-order-result")"
    cat "$WORK/cli-third-order-result" >>"$LOG"
    end
  }
done
for cli_third_cwd in forbidden wildcard wildcard-relative fixed-equal fixed-mismatch fixed-default rule-wildcard rule-wildcard-relative rule-fixed; do
  begin "cli-core-third-editcwd-$cli_third_cwd" && {
    cli_core_third_order_compare editcwd "$cli_third_cwd" >"$WORK/cli-third-order-result" 2>&1 || fail "$(cat "$WORK/cli-third-order-result")"
    cat "$WORK/cli-third-order-result" >>"$LOG"
    end
  }
done
for cli_third_root in missing existing unreadable; do
  begin "cli-core-third-rootprivacy-$cli_third_root" && {
    cli_core_third_order_compare rootprivacy "$cli_third_root" >"$WORK/cli-third-order-result" 2>&1 || fail "$(cat "$WORK/cli-third-order-result")"
    cat "$WORK/cli-third-order-result" >>"$LOG"
    end
  }
done
