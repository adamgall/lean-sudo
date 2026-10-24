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
