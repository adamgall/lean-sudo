# Residual sudo.ws compatibility: authentication disposition, lookup and auditing.
begin shell-residual-noninteractive-empty-password && {
  install -m 0440 /dev/stdin /etc/sudoers.d/shell-residual <<'EOF'
ivan ALL=(root) /usr/bin/true
EOF
  passwd -d ivan >/dev/null
  run ivan 'sudo -nk /usr/bin/true'
  expect_rc 1
  expect_err_has 'a password is required'
  printf 'ivan:ivanpw\n' | chpasswd
  end
}

begin shell-residual-noninteractive-auth-option && {
  cat >/etc/pam.d/shell-residual <<'EOF'
auth required pam_permit.so
account required pam_permit.so
session required pam_permit.so
EOF
  install -m 0440 /dev/stdin /etc/sudoers.d/shell-residual <<'EOF'
Defaults:judy pam_service=shell-residual
judy ALL=(root) /usr/bin/true
EOF
  run judy 'sudo -nk /usr/bin/true'
  expect_rc 1
  expect_err_has 'a password is required'
  printf 'Defaults:judy noninteractive_auth\n' >>/etc/sudoers.d/shell-residual
  run judy 'sudo -nk /usr/bin/true'
  expect_rc 0
  rm -f /etc/pam.d/shell-residual
  end
}

begin shell-residual-visiblepw && {
  install -m 0440 /dev/stdin /etc/sudoers.d/shell-residual <<'EOF'
Defaults:alice visiblepw
EOF
  run alice "printf 'alicepw\n' | sudo -k /usr/bin/true"
  expect_rc 0
  expect_err_has '[sudo] password for alice:'
  expect_err_lacks 'a terminal is required'
  end
}

begin shell-residual-eof-counts-prior-attempts && {
  rm -f /var/log/shell-residual.log
  install -m 0440 /dev/stdin /etc/sudoers.d/shell-residual <<'EOF'
Defaults:alice logfile=/var/log/shell-residual.log,passwd_tries=3
EOF
  run alice "printf 'wrong\n' | sudo -kS /usr/bin/true"
  expect_rc 1
  expect_err_has '1 incorrect password attempt'
  expect_err_lacks '3 incorrect password attempts'
  grep -qF '1 incorrect password attempt' /var/log/shell-residual.log || fail 'missing auth failure count in logfile'
  end
}

begin shell-residual-empty-input-file-event && {
  rm -f /var/log/shell-residual.log
  install -m 0440 /dev/stdin /etc/sudoers.d/shell-residual <<'EOF'
Defaults:alice logfile=/var/log/shell-residual.log
EOF
  run alice 'sudo -kS /usr/bin/true </dev/null'
  expect_rc 1
  expect_err_has 'no password was provided'
  expect_err_has 'a password is required'
  grep -qF 'a password is required' /var/log/shell-residual.log || fail 'missing file-only password-required event'
  ! grep -qF 'incorrect password attempt' /var/log/shell-residual.log || fail 'empty input counted as bad password'
  end
}

begin shell-residual-noninteractive-pseudocommands-unlogged && {
  rm -f /var/log/shell-residual.log
  install -m 0440 /dev/stdin /etc/sudoers.d/shell-residual <<'EOF'
Defaults:alice logfile=/var/log/shell-residual.log
EOF
  run alice 'sudo -nk -l'
  expect_rc 1
  expect_err_has 'a password is required'
  [[ ! -s /var/log/shell-residual.log ]] || fail 'noninteractive list failure logged'
  run alice 'sudo -nk -v'
  expect_rc 1
  [[ ! -s /var/log/shell-residual.log ]] || fail 'noninteractive validation failure logged'
  run alice 'sudo -nk /usr/bin/true'
  expect_rc 1
  grep -qF 'a password is required' /var/log/shell-residual.log || fail 'noninteractive command failure not logged'
  end
}

begin shell-residual-denied-command-auth-log && {
  rm -f /var/log/shell-residual.log
  install -m 0440 /dev/stdin /etc/sudoers.d/shell-residual <<'EOF'
Defaults:bob logfile=/var/log/shell-residual.log,passwd_tries=1
EOF
  run bob "printf 'wrong\n' | sudo -kS /usr/bin/true"
  expect_rc 1
  expect_err_has '1 incorrect password attempt'
  grep -qF 'user NOT in sudoers' /var/log/shell-residual.log || fail 'missing policy denial'
  grep -qF '1 incorrect password attempt' /var/log/shell-residual.log || fail 'missing file-only auth event preceding denial'
  end
}

begin shell-residual-log-denied-file-only && {
  rm -f /var/log/shell-residual.log
  install -m 0440 /dev/stdin /etc/sudoers.d/shell-residual <<'EOF'
Defaults:alice logfile=/var/log/shell-residual.log,passwd_tries=1,!log_denied
EOF
  run alice "printf 'wrong\n' | sudo -kS /usr/bin/true"
  expect_rc 1
  expect_err_has '1 incorrect password attempt'
  grep -qF '1 incorrect password attempt' /var/log/shell-residual.log || fail 'missing file-only auth event with log_denied disabled'
  end
}

begin shell-residual-real-gid && {
  install -m 0440 /dev/stdin /etc/sudoers.d/shell-residual <<'EOF'
ivan ALL=(root) NOPASSWD: /usr/bin/printenv
EOF
  run root 'setpriv --reuid=ivan --regid=adm --init-groups sudo -n /usr/bin/printenv SUDO_GID'
  expect_rc 0
  expect_out_line "$(getent group adm | cut -d: -f3)"
  end
}

begin shell-residual-ignore-dot && {
  install -m 0440 /dev/stdin /etc/sudoers.d/shell-residual <<'EOF'
Defaults:judy !secure_path
judy ALL=(root) NOPASSWD: ALL
EOF
  printf '#!/bin/sh\nprintf "from-dot\\n"\n' >/home/judy/shell-dot-command
  chmod 0755 /home/judy/shell-dot-command
  run judy 'PATH=.:/usr/bin sudo -n shell-dot-command'
  expect_rc 1
  expect_err_has 'ignoring "shell-dot-command" found in '\''.'\'''
  expect_err_has 'Use "sudo ./shell-dot-command"'
  printf 'Defaults:judy !ignore_dot\n' >>/etc/sudoers.d/shell-residual
  run judy 'PATH=.:/usr/bin sudo -n shell-dot-command'
  expect_rc 0
  expect_out_line 'from-dot'
  rm -f /home/judy/shell-dot-command
  end
}

begin shell-residual-dot-searched-last && {
  install -m 0440 /dev/stdin /etc/sudoers.d/shell-residual <<'EOF'
Defaults:judy !secure_path,!ignore_dot
judy ALL=(root) NOPASSWD: ALL
EOF
  printf '#!/bin/sh\nprintf "wrong-dot\\n"\n' >/home/judy/true
  chmod 0755 /home/judy/true
  run judy 'PATH=.:/usr/bin sudo -n true'
  expect_rc 0
  expect_out_empty
  rm -f /home/judy/true
  end
}

begin shell-residual-path-info-disabled && {
  install -m 0440 /dev/stdin /etc/sudoers.d/shell-residual <<'EOF'
Defaults:judy !path_info
judy ALL=(root) /usr/bin/true
EOF
  run judy "printf 'judypw\n' | sudo -kS command-that-does-not-exist"
  expect_rc 1
  expect_err_has 'not allowed to execute'
  expect_err_lacks 'command not found'
  end
}

begin shell-residual-absolute-sudoedit && {
  printf 'unchanged\n' >/etc/shell-residual-edit
  run root 'SUDO_EDITOR=/usr/bin/true sudo -n /usr/bin/sudoedit /etc/shell-residual-edit'
  expect_rc 0
  expect_err_has "sudoedit doesn't need to be run via sudo"
  expect_err_has 'unchanged'
  rm -f /etc/shell-residual-edit
  end
}

shell_residual_audit_record() {
  python3 - "$1" <<'PY'
import re, sys
text = open("/tmp/shell-residual.audit").read()
decoded = re.sub(r"\\x([0-9a-fA-F]{2})", lambda m: chr(int(m[1], 16)), text)
if not any("nlmsg_type=0x463" in line and "res=" + sys.argv[1] in line
           for line in decoded.splitlines()):
    print(decoded)
    sys.exit(1)
PY
}

begin shell-residual-audit-denial && {
  install -m 0440 /dev/stdin /etc/sudoers.d/shell-residual <<'EOF'
root ALL=(root) !/usr/bin/true
EOF
  run root 'strace -f -s 16384 -e trace=sendto -o /tmp/shell-residual.audit sudo -n /usr/bin/true'
  expect_rc 1
  shell_residual_audit_record failed || fail 'no USER_CMD failure audit record'
  end
}

begin shell-residual-audit-sudoedit && {
  printf 'unchanged\n' >/etc/shell-residual-edit
  run root 'SUDO_EDITOR=/usr/bin/true strace -f -s 16384 -e trace=sendto -o /tmp/shell-residual.audit sudo -ne /etc/shell-residual-edit'
  expect_rc 0
  shell_residual_audit_record success || fail 'no sudoedit USER_CMD success audit record'
  rm -f /etc/shell-residual-edit
  end
}

begin shell-residual-syslog-denied-disabled && {
  install -m 0440 /dev/stdin /etc/sudoers.d/shell-residual <<'EOF'
Defaults:alice passwd_tries=1,!log_denied
EOF
  cat >/tmp/shell-residual-syslog.py <<'PY'
import os, pwd, socket, subprocess
sock = socket.socket(socket.AF_UNIX, socket.SOCK_DGRAM)
sock.bind("/dev/log")
sock.settimeout(0.1)
pw = pwd.getpwnam("alice")
def drop():
    os.initgroups(pw.pw_name, pw.pw_gid)
    os.setgid(pw.pw_gid)
    os.setuid(pw.pw_uid)
try:
    p = subprocess.Popen(["/usr/bin/sudo", "-kS", "/usr/bin/true"],
                         stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                         stderr=subprocess.PIPE, cwd=pw.pw_dir, preexec_fn=drop)
    out, err = p.communicate(b"wrong\n")
    while True:
        try:
            message = sock.recv(16384).decode()
        except socket.timeout:
            break
        if "incorrect password attempt" in message:
            print(message)
finally:
    sock.close()
    os.unlink("/dev/log")
PY
  run root 'python3 /tmp/shell-residual-syslog.py'
  expect_rc 0
  expect_out_empty
  rm -f /tmp/shell-residual-syslog.py
  end
}

begin shell-residual-interrupt-prior-attempt && {
  pty alice 'sudo -k /usr/bin/true' -e 'password for alice: ' -s 'wrong\r' \
    -e 'password for alice: ' -s $'\003'
  expect_rc 130
  expect_out_has '1 incorrect password attempt'
  expect_out_lacks 'no password was provided'
  end
}

begin shell-residual-interrupt-first-attempt && {
  pty alice 'sudo -k /usr/bin/true' -e 'password for alice: ' -s $'\003'
  expect_rc 130
  expect_out_has 'a password is required'
  expect_out_lacks 'incorrect password attempt'
  expect_out_lacks 'no password was provided'
  end
}

begin shell-residual-audit-authentication && {
  install -m 0440 /dev/stdin /etc/sudoers.d/shell-residual <<'EOF'
Defaults:alice passwd_tries=1
EOF
  run root "printf 'wrong\n' | strace -u alice -f -s 16384 -e trace=sendto -o /tmp/shell-residual.audit sudo -kS /usr/bin/true"
  expect_rc 1
  expect_err_has '1 incorrect password attempt'
  shell_residual_audit_record failed || fail 'no authentication USER_CMD failure audit record'
  end
}

begin shell-residual-kernel-timestamp-shared-parent && {
  install -m 0440 /dev/stdin /etc/sudoers.d/shell-residual <<'EOF'
Defaults:alice timestamp_type=kernel
EOF
  pty alice 'sudo -v && sudo -n /usr/bin/true && bash -c '\''sudo -n /usr/bin/true; result=$?; echo nested:$result; exit $result'\''; result=$?; exit $result' \
    -e 'password for alice: ' -s 'alicepw\r'
  expect_rc 0
  expect_out_has 'nested:0'
  end
}

begin shell-residual-ppid-timestamp-parent-isolation && {
  install -m 0440 /dev/stdin /etc/sudoers.d/shell-residual <<'EOF'
Defaults:alice timestamp_type=ppid
EOF
  pty alice 'sudo -v && sudo -n /usr/bin/true && bash -c '\''sudo -n /usr/bin/true; result=$?; echo nested:$result; exit $result'\''; result=$?; exit $result' \
    -e 'password for alice: ' -s 'alicepw\r'
  expect_rc 1
  expect_out_has 'nested:1'
  expect_out_has 'a password is required'
  end
}

begin shell-residual-kernel-timestamp-invalidate-key && {
  install -m 0440 /dev/stdin /etc/sudoers.d/shell-residual <<'EOF'
Defaults:alice timestamp_type=kernel
EOF
  pty alice 'sudo -v && sudo -k && sudo -n /usr/bin/true' \
    -e 'password for alice: ' -s 'alicepw\r'
  expect_rc 0
  end
}

begin shell-residual-tty-timestamp-invalidate-key && {
  install -m 0440 /dev/stdin /etc/sudoers.d/shell-residual <<'EOF'
Defaults:alice timestamp_type=tty
EOF
  pty alice 'sudo -v && sudo -k && sudo -n /usr/bin/true' \
    -e 'password for alice: ' -s 'alicepw\r'
  expect_rc 1
  expect_out_has 'a password is required'
  end
}
