# Shell/PAM compatibility against Ubuntu's sudo.ws 1.9.17p2.

begin shell_prompt_environment && {
  XENV=(SUDO_PROMPT='custom %u on %h: ')
  run alice "printf 'alicepw\n' | sudo -kS /usr/bin/true"
  expect_rc 0
  expect_err_has 'custom alice on '
  end
}

begin shell_bell_stdin && {
  run alice "printf 'alicepw\n' | sudo -kBS /usr/bin/true"
  expect_rc 0
  expect_err_lacks $'\a'
  end
}

begin shell_ssh_no_tty && {
  XENV=(SSH_CONNECTION='127.0.0.1 1000 127.0.0.1 22')
  run alice 'sudo -k /usr/bin/true'
  expect_rc 1
  expect_err_has "either use ssh's -t option or configure an askpass helper"
  end
}

begin shell_askpass_invoking_identity && {
  cat >/usr/local/bin/shell-askpass <<'EOF'
#!/bin/sh
/usr/bin/id -u >&2
printf 'alicepw\n'
EOF
  chmod 0755 /usr/local/bin/shell-askpass
  XENV=(SUDO_ASKPASS=/usr/local/bin/shell-askpass)
  run alice 'sudo -kA /usr/bin/true'
  expect_rc 0
  expect_err_has "$(uid_of alice)"
  rm -f /usr/local/bin/shell-askpass
  end
}

begin shell_askpass_sudo_conf && {
  cp -a /etc/sudo.conf "$WORK/shell-sudo.conf"
  printf 'Path askpass /usr/local/bin/shell-askpass\n' >/etc/sudo.conf
  printf '#!/bin/sh\nprintf "alicepw\\n"\n' >/usr/local/bin/shell-askpass
  chmod 0755 /usr/local/bin/shell-askpass
  run alice 'sudo -kA /usr/bin/true'
  expect_rc 0
  cp -a "$WORK/shell-sudo.conf" /etc/sudo.conf
  rm -f /usr/local/bin/shell-askpass
  end
}

begin shell_askpass_display_fallback && {
  printf '#!/bin/sh\nprintf "alicepw\\n"\n' >/usr/local/bin/shell-askpass
  chmod 0755 /usr/local/bin/shell-askpass
  XENV=(SUDO_ASKPASS=/usr/local/bin/shell-askpass DISPLAY=:99)
  run alice 'sudo -k /usr/bin/true'
  expect_rc 0
  rm -f /usr/local/bin/shell-askpass
  end
}

begin shell_unknown_plugin_refused && {
  cp -a /etc/sudo.conf "$WORK/shell-sudo.conf"
  printf 'Plugin unavailable_approval /does/not/exist.so\n' >/etc/sudo.conf
  run bob 'sudo -n /usr/bin/true'
  expect_rc 1
  expect_err_has 'plugin'
  cp -a "$WORK/shell-sudo.conf" /etc/sudo.conf
  end
}

begin shell_admin_flag && {
  rm -f /home/alice/.sudo_as_admin_successful
  run alice "printf 'alicepw\n' | sudo -kS /usr/bin/true; stat -c '%U %a' ~/.sudo_as_admin_successful"
  expect_rc 0
  expect_out_line 'alice 644'
  end
}

begin shell_controlling_tty_without_stdio && {
  install -m 0440 /dev/stdin /etc/sudoers.d/shell-tty <<'EOF'
Defaults:bob requiretty
bob ALL=(root) NOPASSWD: /usr/bin/true
EOF
  pty bob 'sudo -n /usr/bin/true </dev/null >/tmp/shell-tty-out 2>/tmp/shell-tty-err; echo status:$?'
  expect_rc 0
  expect_out_has 'status:0'
  end
}

begin shell_logfile_format && {
  rm -f /tmp/shell-events.log
  install -m 0440 /dev/stdin /etc/sudoers.d/shell-log <<'EOF'
Defaults:bob logfile=/tmp/shell-events.log,log_year,log_host,loglinelen=0
bob ALL=(root) NOPASSWD: /usr/bin/true
EOF
  run bob 'sudo -n /usr/bin/true'
  expect_rc 0
  run root 'cat /tmp/shell-events.log'
  expect_rc 0
  expect_out_has ' : bob : HOST='
  expect_out_has 'PWD=/home/bob ; USER=root ; COMMAND=/usr/bin/true'
  end
}

begin shell_logfile_auth_failure && {
  rm -f /tmp/shell-events.log
  install -m 0440 /dev/stdin /etc/sudoers.d/shell-log <<'EOF'
Defaults:alice logfile=/tmp/shell-events.log,loglinelen=0,passwd_tries=1
EOF
  run alice "printf 'wrong\n' | sudo -kS /usr/bin/true"
  expect_rc 1
  run root 'cat /tmp/shell-events.log'
  expect_rc 0
  expect_out_has '1 incorrect password attempt ; PWD=/home/alice ; USER=root ; COMMAND=/usr/bin/true'
  end
}

begin shell_mail_headers_and_identity && {
  rm -f /tmp/shell-mail-body /tmp/shell-mail-identity
  cat >/usr/local/bin/shell-sendmail <<'EOF'
#!/bin/sh
/usr/bin/id >/tmp/shell-mail-identity
printf 'flags:%s\n' "$*" >>/tmp/shell-mail-identity
cat >/tmp/shell-mail-body
EOF
  chmod 0755 /usr/local/bin/shell-sendmail
  install -m 0440 /dev/stdin /etc/sudoers.d/shell-mail <<'EOF'
Defaults mailerpath=/usr/local/bin/shell-sendmail,mailerflags="-t -i",mailto=admin@example.test,mailfrom=sudo@example.test,mailsub="incident on %h",mail_no_user
EOF
  run ivan "printf 'ivanpw\n' | sudo -S /usr/bin/true"
  expect_rc 1
  run root 'for n in 1 2 3 4 5; do test -s /tmp/shell-mail-body && break; sleep 1; done; cat /tmp/shell-mail-identity /tmp/shell-mail-body'
  expect_rc 0
  expect_out_has "uid=$(uid_of ivan)(ivan) gid=$(gid_of ivan)(ivan) groups=$(gid_of ivan)(ivan)"
  expect_out_has 'flags:-t -i'
  expect_out_has 'To: admin@example.test'
  expect_out_has 'From: sudo@example.test'
  expect_out_has 'Auto-Submitted: auto-generated'
  expect_out_has 'Subject: incident on '
  rm -f /usr/local/bin/shell-sendmail
  end
}

begin shell_pam_disabled_account_session && {
  install -m 0440 /dev/stdin /etc/sudoers.d/shell-pam <<'EOF'
Defaults:bob !pam_acct_mgmt,!pam_setcred,!pam_session,!pam_ruser,pam_rhost
bob ALL=(root) NOPASSWD: /usr/bin/true
EOF
  run bob 'sudo -n /usr/bin/true'
  expect_rc 0
  end
}

begin shell_insults_enabled && {
  install -m 0440 /dev/stdin /etc/sudoers.d/shell-insults <<'EOF'
Defaults:alice insults,passwd_tries=2
EOF
  run alice "printf 'wrong\nalicepw\n' | sudo -kS /usr/bin/true"
  expect_rc 0
  expect_err_lacks 'Sorry, try again.'
  end
}

begin shell_lecture_once_custom && {
  printf 'A custom administrator lecture.\n' >/etc/shell-lecture
  install -m 0440 /dev/stdin /etc/sudoers.d/shell-lecture <<'EOF'
Defaults:alice lecture=once,lecture_file=/etc/shell-lecture
EOF
  run alice "printf 'alicepw\n' | sudo -kS /usr/bin/true"
  expect_rc 0
  expect_err_has 'A custom administrator lecture.'
  run alice "printf 'alicepw\n' | sudo -kS /usr/bin/true"
  expect_rc 0
  expect_err_lacks 'A custom administrator lecture.'
  rm -f /etc/shell-lecture
  end
}

begin shell_password_timeout && {
  install -m 0440 /dev/stdin /etc/sudoers.d/shell-timeout <<'EOF'
Defaults:alice passwd_timeout=0.05
EOF
  run alice 'sleep 5 | sudo -kS /usr/bin/true'
  expect_rc 1
  expect_err_has 'timed out reading password'
  end
}

begin shell_sudo_conf_case_insensitive_plugins && {
  cp -a /etc/sudo.conf "$WORK/shell-sudo.conf"
  printf 'pLuGiN unavailable_approval /does/not/exist.so\n' >/etc/sudo.conf
  run bob 'sudo -n /usr/bin/true'
  expect_rc 1
  expect_err_has 'plugin'
  cp -a "$WORK/shell-sudo.conf" /etc/sudo.conf
  end
}

begin shell_pam_session_error_nonfatal && {
  cat >/etc/pam.d/shell-session-error <<'EOF'
auth required pam_permit.so
account required pam_permit.so
session required pam_deny.so
EOF
  install -m 0440 /dev/stdin /etc/sudoers.d/shell-session <<'EOF'
Defaults:judy pam_service=shell-session-error
judy ALL=(root) /usr/bin/true
EOF
  run judy 'sudo -S /usr/bin/true'
  expect_rc 0
  rm -f /etc/pam.d/shell-session-error
  end
}

begin shell_pam_account_error_specific && {
  cat >/etc/pam.d/shell-account-error <<'EOF'
auth required pam_permit.so
account required pam_deny.so
session required pam_permit.so
EOF
  install -m 0440 /dev/stdin /etc/sudoers.d/shell-account <<'EOF'
Defaults:judy pam_service=shell-account-error
judy ALL=(root) /usr/bin/true
EOF
  run judy 'sudo -S /usr/bin/true'
  expect_rc 1
  expect_err_has 'account validation failure, is your account locked?'
  rm -f /etc/pam.d/shell-account-error
  end
}

begin shell_pam_validate_expired_account && {
  install -m 0440 /dev/stdin /etc/sudoers.d/shell-expired <<'EOF'
Defaults:judy timestamp_type=global
judy ALL=(root) /usr/bin/true
EOF
  chage -E 0 judy
  run judy "printf 'judypw\n' | sudo -S -v"
  expect_rc 1
  expect_err_has 'account validation failure, is your account locked?'
  chage -E -1 judy
  run judy 'sudo -n /usr/bin/true'
  expect_rc 1
  expect_err_has 'a password is required'
  end
}

begin shell_pam_list_expired_account && {
  install -m 0440 /dev/stdin /etc/sudoers.d/shell-expired <<'EOF'
Defaults:judy timestamp_type=global
judy ALL=(root) /usr/bin/true
EOF
  chage -E 0 judy
  run judy "printf 'judypw\n' | sudo -S -l"
  expect_rc 1
  expect_err_has 'account validation failure, is your account locked?'
  chage -E -1 judy
  run judy 'sudo -n /usr/bin/true'
  expect_rc 1
  expect_err_has 'a password is required'
  end
}

begin shell_sudo_conf_group_writable_ignored && {
  cp -a /etc/sudo.conf "$WORK/shell-sudo.conf"
  printf 'Path noexec /nonexistent/noexec.so\n' >/etc/sudo.conf
  chown root:adm /etc/sudo.conf
  chmod 0664 /etc/sudo.conf
  install -m 0440 /dev/stdin /etc/sudoers.d/shell-noexec <<'EOF'
judy ALL=(root) NOPASSWD: NOEXEC: /usr/bin/sh
EOF
  run judy 'sudo -n /usr/bin/sh -c /usr/bin/true'
  expect_rc 126
  expect_err_has 'sudo: /etc/sudo.conf is group writable'
  expect_err_has 'Permission denied'
  expect_err_lacks '/nonexistent/noexec.so'
  cp -a "$WORK/shell-sudo.conf" /etc/sudo.conf
  end
}
