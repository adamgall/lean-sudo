

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
  mkdir -p /run/sshd "$WORK/ssh"
  ssh-keygen -q -t ed25519 -N '' -f "$WORK/ssh/id"
  cp "$WORK/ssh/id.pub" "$WORK/ssh/authorized_keys"
  chmod 0755 "$WORK/ssh"
  cat >"$WORK/ssh/sshd_config" <<EOF
ListenAddress 127.0.0.1
Port 2222
HostKey /etc/ssh/ssh_host_ed25519_key
PidFile $WORK/ssh/sshd.pid
AuthorizedKeysFile $WORK/ssh/authorized_keys
PasswordAuthentication no
KbdInteractiveAuthentication no
UsePAM yes
AllowUsers alice
StrictModes no
EOF
  /usr/sbin/sshd -D -e -f "$WORK/ssh/sshd_config" >"$WORK/ssh/daemon.log" 2>&1 &
  shell_sshd_pid=$!
  for ((shell_wait=0; shell_wait<100; shell_wait++)); do
    ssh-keyscan -T 1 -p 2222 127.0.0.1 >"$WORK/ssh/known_hosts" 2>/dev/null && break
    kill -0 "$shell_sshd_pid" 2>/dev/null || break
    sleep 0.05
  done
  run root "ssh -T -i '$WORK/ssh/id' -p 2222 -o BatchMode=yes -o UserKnownHostsFile='$WORK/ssh/known_hosts' alice@127.0.0.1 'test -n \"\$SSH_CONNECTION\" && test -z \"\$SSH_TTY\" && exec sudo -k /usr/bin/true'"
  expect_rc 1
  expect_err_has "either use ssh's -t option or configure an askpass helper"
  kill "$shell_sshd_pid" 2>/dev/null
  wait "$shell_sshd_pid" 2>/dev/null
  end
}



shell_run_askpass() {
  local mode=$1 xvfb_pid driver_pid
  Xvfb :99 -screen 0 640x480x24 -nolisten tcp -ac >"$WORK/askpass-xvfb.log" 2>&1 &
  xvfb_pid=$!
  for ((shell_wait=0; shell_wait<100; shell_wait++)); do
    DISPLAY=:99 xdotool getdisplaygeometry >/dev/null 2>&1 && break
    kill -0 "$xvfb_pid" 2>/dev/null || break
    sleep 0.05
  done
  rm -f "$WORK/askpass.uid"
  DISPLAY=:99 python3 - "$WORK/askpass.uid" <<'PY' &
import glob, os, subprocess, sys, time
helper = os.path.realpath("/usr/bin/ssh-askpass")
deadline = time.monotonic() + 15
while time.monotonic() < deadline:
    windows = subprocess.run(["xdotool", "search", "--onlyvisible", "--class", ".*"],
                             capture_output=True, text=True)
    for proc in glob.glob("/proc/[0-9]*"):
        try:
            if os.readlink(proc + "/exe") != helper:
                continue
            status = open(proc + "/status").read()
        except (FileNotFoundError, PermissionError):
            continue
        if windows.returncode == 0 and windows.stdout.strip():
            uid = next(line for line in status.splitlines() if line.startswith("Uid:"))
            with open(sys.argv[1], "w") as output:
                output.write(" ".join(uid.split()[1:]))
            window = windows.stdout.splitlines()[0]
            subprocess.run(["xdotool", "windowfocus", "--sync", window], check=True)
            subprocess.run(["xdotool", "type", "--window", window, "alicepw"], check=True)
            subprocess.run(["xdotool", "key", "--window", window, "Return"], check=True)
            sys.exit(0)
    time.sleep(0.05)
raise SystemExit("askpass window/process did not become ready")
PY
  driver_pid=$!
  XENV=(DISPLAY=:99)
  [[ $mode == conf ]] || XENV+=(SUDO_ASKPASS=/usr/bin/ssh-askpass)
  if [[ $mode == display ]]; then
    run alice 'sudo -k /usr/bin/true'
  else
    run alice 'sudo -kA /usr/bin/true'
  fi
  expect_rc 0
  wait "$driver_pid" || fail 'could not drive the real askpass window'
  [[ $(cat "$WORK/askpass.uid" 2>/dev/null) == "$(uid_of alice) $(uid_of alice) $(uid_of alice) $(uid_of alice)" ]] ||
    fail 'askpass did not run with the invoking user credentials'
  kill "$xvfb_pid" 2>/dev/null
  wait "$xvfb_pid" 2>/dev/null
}

begin shell_askpass_invoking_identity && {
  shell_run_askpass environment
  end
}

begin shell_askpass_sudo_conf && {
  cp -a /etc/sudo.conf "$WORK/shell-sudo.conf"
  printf 'Path askpass /usr/bin/ssh-askpass\n' >/etc/sudo.conf
  shell_run_askpass conf
  cp -a "$WORK/shell-sudo.conf" /etc/sudo.conf
  end
}

begin shell_askpass_display_fallback && {
  shell_run_askpass display
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
  rm -f /var/mail/root
  install -o Debian-exim -g adm -m 0640 /dev/null /var/log/exim4/mainlog
  install -m 0440 /dev/stdin /etc/sudoers.d/shell-mail <<'EOF'
Defaults mailerpath=/usr/sbin/sendmail,mailerflags="-t -i",mailto=admin@example.test,mailfrom=sudo@example.test,mailsub="incident on %h",mail_no_user
EOF
  run root "printf 'ivanpw\n' | strace -f -s 4096 -e trace=execve,setgroups,setresuid,setresgid,setuid,setgid -o '$WORK/shell-mail.trace' runuser -u ivan -- sudo -S /usr/bin/true"
  expect_rc 1
  run root 'python3 -c '"'"'import pathlib,time; p=pathlib.Path("/var/mail/root"); deadline=time.monotonic()+10
while not p.exists() or "Auto-Submitted: auto-generated" not in p.read_text():
    assert time.monotonic()<deadline, "mail delivery timed out"
    time.sleep(.01)
print(p.read_text())
print(pathlib.Path("/var/log/exim4/mainlog").read_text())'"'"
  expect_rc 0
  expect_out_has 'U=ivan P=local'
  expect_out_has 'To: admin@example.test'
  expect_out_has 'From: sudo@example.test'
  expect_out_has 'Auto-Submitted: auto-generated'
  expect_out_has 'Subject: incident on '
  run root "cat '$WORK/shell-mail.trace'"
  expect_rc 0
  expect_out_has 'execve("/usr/sbin/sendmail", ["sendmail", "-t", "-i"]'
  expect_out_has "setgroups(1, [$(gid_of ivan)])"
  expect_out_has "setgid($(gid_of ivan))"
  expect_out_has "setuid($(uid_of ivan))"
  rm -f "$WORK/shell-mail.trace"
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

  printf 'root hard nofile 1073741824\n' >/etc/security/limits.d/shell-session.conf
  install -m 0440 /dev/stdin /etc/sudoers.d/shell-session <<'EOF'
Defaults:judy pam_session
judy ALL=(root) /usr/bin/true
EOF
  cat >"$WORK/shell-session.py" <<'PY'
import subprocess, sys
sys.path.insert(0, "/usr/local/lib")
from sudo_it_logging import Syslog
with Syslog() as log:
    result = subprocess.run(["setpriv", "--reuid=judy", "--regid=judy", "--init-groups",
                             "sudo", "-kS", "/usr/bin/true"], input="judypw\n",
                            capture_output=True, text=True)
    sys.stdout.write(result.stdout)
    sys.stderr.write(result.stderr)
    messages = "\n".join(log.messages())
    print(messages)
    assert result.returncode == 0, result.returncode
    assert "pam_limits(sudo:session)" in messages and "Could not set limit" in messages
PY
  run root "python3 '$WORK/shell-session.py'"
  expect_rc 0
  rm -f /etc/security/limits.d/shell-session.conf
  end
}

begin shell_pam_account_error_specific && {
  install -m 0440 /dev/stdin /etc/sudoers.d/shell-account <<'EOF'
judy ALL=(root) /usr/bin/true
EOF
  chage -E 0 judy
  run judy "printf 'judypw\n' | sudo -kS /usr/bin/true"
  expect_rc 1
  expect_err_has 'account validation failure, is your account locked?'
  chage -E -1 judy
  end
}



shell_expect_expired_account_stderr() {
  local expected=$'[sudo] password for judy: sudo: account validation failure, is your account locked?\nsudo: a password is required'
  [[ $ERR == "$expected" ]] || fail "expired account stderr differs: $ERR"
}

begin shell_pam_validate_expired_account && {
  install -m 0440 /dev/stdin /etc/sudoers.d/shell-expired <<'EOF'
Defaults:judy timestamp_type=global
judy ALL=(root) /usr/bin/true
EOF
  chage -E 0 judy
  run judy "printf 'judypw\n' | sudo -S -v"
  expect_rc 1
  shell_expect_expired_account_stderr
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
  shell_expect_expired_account_stderr
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

begin shell_pam_run_expired_account && {
  install -m 0440 /dev/stdin /etc/sudoers.d/shell-expired <<'EOF'
Defaults:judy timestamp_type=global
judy ALL=(root) /usr/bin/true
EOF
  chage -E 0 judy
  run judy "printf 'judypw\n' | sudo -S /usr/bin/true"
  expect_rc 1
  shell_expect_expired_account_stderr
  chage -E -1 judy
  run judy 'sudo -n /usr/bin/true'
  expect_rc 1
  expect_err_has 'a password is required'
  end
}
