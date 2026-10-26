
begin ext-core-list-root-no-rules && {
  cat >/etc/sudoers <<'EOF'
Defaults env_reset
EOF
  for opts in '-l' '-ll' '-U root -l'; do
    run root "sudo $opts"
    expect_rc 0
    expect_out_line "User root is not allowed to run sudo on $host."
    [[ -z $ERR ]] || fail "stderr: expected empty for sudo $opts"
  done
  run root 'sudo -l true'
  expect_rc 1
  expect_out_empty
  [[ -z $ERR ]] || fail 'stderr: expected empty for sudo -l true'
  end
}

begin ext-core-list-other-no-rules && {
  run root 'sudo -U ivan -l'
  expect_rc 0
  expect_out_line "User ivan is not allowed to run sudo on $host."
  [[ -z $ERR ]] || fail 'stderr: expected empty'
  run root 'sudo -U ivan -l true'
  expect_rc 1
  expect_out_empty
  end
}

begin ext-core-list-perms-other-no-rules && {
  install -m 0440 /dev/stdin /etc/sudoers.d/ext-core <<'EOF'
judy ALL=(ALL:ALL) NOPASSWD: list
EOF
  run judy 'sudo -l -U ivan'
  expect_rc 0
  expect_out_line "User ivan is not allowed to run sudo on $host."
  [[ -z $ERR ]] || fail 'stderr: expected empty'
  run judy 'sudo -l -U ivan true'
  expect_rc 1
  expect_out_empty
  end
}

begin ext-core-list-validated-no-denial-log && {
  install -m 0440 /dev/stdin /etc/sudoers.d/ext-core <<'EOF'
judy ALL=(ALL:ALL) NOPASSWD: list
EOF
  cat >"$WORK/ext-core-syslog.py" <<'PY'
import subprocess, sys
sys.path.insert(0, "/usr/local/lib")
from sudo_it_logging import Syslog
with Syslog() as log:
    for user, args in (("root", ["-U", "ivan", "-l"]), ("judy", ["-l", "-U", "ivan"])):
        result = subprocess.run(["setpriv", "--reuid=" + user, "--regid=" + user,
                                 "--init-groups", "sudo", *args],
                                capture_output=True, text=True, stdin=subprocess.DEVNULL)
        assert result.returncode == 0, (user, result.returncode, result.stderr)
    for message in log.messages():
        if "COMMAND=" in message or "not allowed" in message:
            print(message)
PY
  run root "python3 '$WORK/ext-core-syslog.py'"
  expect_rc 0
  expect_out_empty
  end
}

begin ext-core-list-command-no-rules && {
  run ivan 'echo ivanpw | sudo -S -l true'
  expect_rc 1
  expect_err_has "Sorry, user ivan may not run sudo on $host."
  run ivan 'echo ivanpw | sudo -S -u judy -l true'
  expect_rc 1
  expect_err_has "Sorry, user ivan may not run sudo on $host."
  install -m 0440 /dev/stdin /etc/sudoers.d/ext-core <<'EOF'
ivan ALL=(ALL:ALL) /dev/null
EOF
  run ivan 'echo ivanpw | sudo -S -l true'
  expect_rc 1
  expect_out_empty
  expect_err_lacks 'Sorry'
  end
}

begin ext-core-list-denial-typed-command && {
  run ivan "echo ivanpw | sudo -S -U judy -l true 'x y'"
  expect_rc 1
  expect_err_has "Sorry, user ivan is not allowed to execute 'list true x y' as judy on $host."
  run ivan 'echo ivanpw | sudo -S -U judy -u judy -l true'
  expect_rc 1
  expect_err_has "Sorry, user ivan is not allowed to execute 'list true' as judy on $host."
  run ivan 'echo ivanpw | sudo -S -U ivan -l'
  expect_rc 1
  expect_err_has "Sorry, user ivan is not allowed to execute 'list' as ivan on $host."
  end
}

begin ext-core-list-pam-account-denied && {
  printf '%s\n' 'auth sufficient pam_permit.so' 'account requisite pam_deny.so' \
    'session optional pam_permit.so' >/etc/pam.d/ext-core-deny
  install -m 0440 /dev/stdin /etc/sudoers.d/ext-core <<'EOF'
Defaults pam_service=ext-core-deny
judy ALL=(root) NOPASSWD: /usr/bin/true
EOF
  for cmd in 'sudo -n -l' 'sudo -n -l true' 'sudo -n true'; do
    run judy "$cmd"
    expect_rc 1
    expect_out_empty
    expect_err_has 'sudo: account validation failure, is your account locked?'
    expect_err_has 'sudo: a password is required'
  done
  run root 'sudo -l'
  expect_rc 1
  expect_out_empty
  expect_err_has 'sudo: account validation failure, is your account locked?'
  rm -f /etc/pam.d/ext-core-deny
  end
}

begin ext-core-path-unset-no-search && {
  cat >/etc/sudoers <<'EOF'
Defaults env_reset
root ALL=(ALL:ALL) ALL
EOF
  run root 'unset PATH; /usr/bin/sudo true'
  expect_rc 1
  expect_err_has 'sudo: true: command not found'
  run root '/usr/bin/env -i /usr/bin/sudo -l true'
  expect_rc 1
  expect_out_empty
  expect_err_has 'sudo: true: command not found'
  run root '/usr/bin/env -i /usr/bin/sudo -l /usr/bin/true'
  expect_rc 0
  expect_out_line '/usr/bin/true'
  end
}

begin ext-core-path-unset-secure-path && {
  run root 'unset PATH; /usr/bin/sudo true'
  expect_rc 0
  run root '/usr/bin/env -i /usr/bin/sudo -l true'
  expect_rc 0
  expect_out_line '/usr/bin/true'
  end
}

begin ext-core-shell-not-found && {
  run root 'SHELL=/nonexistent/ext-core-shell sudo -s'
  expect_rc 1
  expect_err_has 'sudo: /nonexistent/ext-core-shell: command not found'
  run root 'SHELL=/nonexistent/ext-core-shell sudo -s true'
  expect_rc 1
  expect_err_has 'sudo: /nonexistent/ext-core-shell: command not found'
  printf '#!/bin/sh\n' >/root/ext-core-shell
  chmod 0644 /root/ext-core-shell
  run root 'SHELL=/root/ext-core-shell sudo -s'
  expect_rc 1
  expect_err_has 'sudo: /root/ext-core-shell: command not found'
  rm -f /root/ext-core-shell
  getent passwd ext-core-login >/dev/null ||
    useradd -s /nonexistent/ext-core-login ext-core-login 2>/dev/null
  run root 'sudo -u ext-core-login -i'
  expect_rc 1
  expect_err_has 'sudo: /nonexistent/ext-core-login: command not found'
  end
}

begin ext-core-version-io-errors && {
  run root 'sudo --version >/dev/full; echo rc=$?'
  expect_out_line 'rc=0'
  [[ -z $ERR ]] || fail 'stderr: expected empty for /dev/full'
  run root 'sudo -V >&-; echo rc=$?'
  expect_out_line 'rc=0'
  [[ -z $ERR ]] || fail 'stderr: expected empty for closed stdout'
  run root 'bash -c '\''sudo --version | true; echo rc=${PIPESTATUS[0]}'\'''
  expect_out_line 'rc=0'
  [[ -z $ERR ]] || fail 'stderr: expected empty for closed pipe'
  run ivan 'sudo -V >/dev/full; echo rc=$?'
  expect_out_line 'rc=0'
  [[ -z $ERR ]] || fail 'stderr: expected empty for unprivileged /dev/full'
  end
}

begin ext-core-deny-runas-self-no-auth && {
  install -m 0440 /dev/stdin /etc/sudoers.d/ext-core <<'EOF'
ALL ALL=(judy) NOPASSWD: /usr/bin/true, sudoedit
EOF
  run ivan 'sudo -u ivan /usr/bin/true'
  expect_rc 1
  [[ $ERR == "Sorry, user ivan is not allowed to execute '/usr/bin/true' as ivan on $host." ]] ||
    fail 'stderr: expected only the denial'
  run ivan 'sudoedit -u ivan /tmp/ext-core-file'
  expect_rc 1
  expected="Sorry, user ivan is not allowed to execute 'sudoedit /tmp/ext-core-file' as ivan on $host."
  [[ $ERR == "$expected" ]] || fail 'stderr: expected only the sudoedit denial'
  run ivan 'sudoedit -u root /tmp/ext-core-file'
  expect_rc 1
  expect_err_has 'sudoedit: a terminal is required to read the password'
  expect_err_has 'sudoedit: a password is required'
  expect_err_lacks 'sudo: '
  run ivan 'sudo -u root /usr/bin/true'
  expect_rc 1
  expect_err_has 'sudo: a password is required'
  end
}

begin ext-core-validate-root-no-rules && {
  cat >/etc/sudoers <<'EOS'
Defaults env_reset
EOS
  run root 'sudo -v'
  expect_rc 0
  expect_out_empty
  [[ -z $ERR ]] || fail 'stderr: expected empty'
  end
}

begin ext-core-negated-nopasswd-denial && {
  install -m 0440 /dev/stdin /etc/sudoers.d/ext-core <<'EOS'
ivan ALL=(ALL:ALL) NOPASSWD: ALL, !/usr/bin/id
EOS
  run ivan 'sudo -n /usr/bin/id'
  expect_rc 1
  [[ $ERR == "Sorry, user ivan is not allowed to execute '/usr/bin/id' as root on $host." ]] ||
    fail 'stderr: expected only the denial'
  end
}

begin ext-core-list-other-nopasswd-all && {
  install -m 0440 /dev/stdin /etc/sudoers.d/ext-core <<'EOS'
judy ALL=(ALL:ALL) NOPASSWD: ALL
EOS
  run judy 'sudo -ll -U kate'
  expect_rc 0
  expect_out_line "User kate is not allowed to run sudo on $host."
  [[ -z $ERR ]] || fail 'stderr: expected empty'
  end
}

begin ext-core-sudoedit-refused-no-pam-session && {
  install -m 0440 /dev/stdin /etc/sudoers.d/ext-core <<'EOS'
ivan ALL=(ALL:ALL) NOPASSWD: ALL
EOS
  printf 'original\n' >/tmp/ext-core-edit
  cat >"$WORK/ext-core-edit.py" <<'PY'
import subprocess, sys
sys.path.insert(0, "/usr/local/lib")
from sudo_it_logging import Syslog
with Syslog() as log:
    result = subprocess.run(["setpriv", "--reuid=ivan", "--regid=ivan", "--init-groups",
                             "env", "SUDO_EDITOR=/usr/bin/true", "sudo", "-e",
                             "/tmp/ext-core-edit"],
                            capture_output=True, text=True, stdin=subprocess.DEVNULL)
    sys.stderr.write(result.stderr)
    print("rc=%d" % result.returncode)
    for message in log.messages():
        if "pam_unix" in message:
            print(message)
PY
  run root "python3 '$WORK/ext-core-edit.py'"
  expect_rc 0
  expect_out_line 'rc=1'
  expect_out_lacks 'pam_unix'
  expect_err_has 'editing files in a writable directory is not permitted'
  rm -f /tmp/ext-core-edit
  end
}

ext_core_env_keys() {
  XENV=(TERM=xterm MAIL=/var/mail/ivan SUDO_USER=stale)
  run ivan "sudo /usr/bin/env | cut -d= -f1 | tr '\n' ' '"
  expect_rc 0
  [[ ${OUT% } == "$*" ]] || fail "env order: expected '$*', got '$OUT'"
}

begin ext-core-env-order-reset && {
  install -m 0440 /dev/stdin /etc/sudoers.d/ext-core <<'EOS'
ivan ALL=(ALL:ALL) NOPASSWD: ALL
EOS
  ext_core_env_keys TERM PATH LANG MAIL LOGNAME USER HOME SHELL \
    SUDO_COMMAND SUDO_USER SUDO_UID SUDO_GID SUDO_HOME
  end
}

begin ext-core-env-order-copy && {
  install -m 0440 /dev/stdin /etc/sudoers.d/ext-core <<'EOS'
Defaults:ivan !env_reset
ivan ALL=(ALL:ALL) NOPASSWD: ALL
EOS
  ext_core_env_keys MAIL USER HOME OLDPWD LOGNAME TERM PATH LANG SHELL SUDO_USER PWD \
    SUDO_COMMAND SUDO_UID SUDO_GID SUDO_HOME
  end
}

begin ext-core-env-order-kept-home && {
  install -m 0440 /dev/stdin /etc/sudoers.d/ext-core <<'EOS'
Defaults:ivan env_keep+="HOME MAIL"
ivan ALL=(ALL:ALL) NOPASSWD: ALL
EOS
  ext_core_env_keys MAIL HOME TERM PATH LANG LOGNAME USER SHELL \
    SUDO_COMMAND SUDO_USER SUDO_UID SUDO_GID SUDO_HOME
  end
}

begin ext-core-shell-args-unescape && {
  install -m 0440 /dev/stdin /etc/sudoers.d/ext-core <<'EOS'
ivan ALL=(ALL:ALL) NOPASSWD: /bin/bash -c echo c d, /usr/bin/printenv
EOS
  run ivan 'sudo -n -s echo c d'
  expect_rc 0
  expect_out_line 'c d'
  run ivan "sudo -n -s echo 'c d'"
  expect_rc 1
  expect_err_has 'a password is required'
  install -m 0440 /dev/stdin /etc/sudoers.d/ext-core-all <<'EOS'
ivan ALL=(ALL:ALL) NOPASSWD: ALL
EOS
  run ivan "sudo -s printenv SUDO_COMMAND 'a b' 'c\\d' 'e\$f' 's\"t'"
  expect_out_line '/bin/bash -c printenv SUDO_COMMAND a\ b c\d e$f s"t'
  end
}

begin ext-core-mail-only-denial-logfile && {
  rm -f /var/log/ext-core.log
  install -m 0440 /dev/stdin /etc/sudoers.d/ext-core <<'EOS'
Defaults logfile=/var/log/ext-core.log, !log_denied, mail_no_perms
ivan ALL=(root) NOPASSWD: /usr/bin/true, !/usr/bin/id
EOS
  run ivan 'sudo -n /usr/bin/id'
  expect_rc 1
  expect_err_has 'This incident has been reported to the administrator.'
  run root 'cat /var/log/ext-core.log'
  expect_out_has 'command not allowed'
  expect_out_has 'COMMAND=/usr/bin/id'
  rm -f /var/log/ext-core.log
  end
}

ext_core_gone_edit() {
  XENV=(SUDO_EDITOR=/usr/bin/true)
  run ivan "rm -rf /tmp/ext-core-gone; mkdir /tmp/ext-core-gone && cd /tmp/ext-core-gone &&
    rmdir /tmp/ext-core-gone && $1"
}

begin ext-core-edit-relative-denied-first && {
  install -m 0440 /dev/stdin /etc/sudoers.d/ext-core <<'EOS'
ivan ALL=(root) NOPASSWD: /usr/bin/true, !sudoedit
EOS
  ext_core_gone_edit 'sudoedit -n foo'
  expect_rc 1
  expect_err_has "Sorry, user ivan is not allowed to execute 'sudoedit foo' as root on $host."
  expect_err_lacks 'writable directory'
  end
}

begin ext-core-edit-relative-accepted-then-refused && {
  rm -f /var/log/ext-core-edit.log
  install -m 0440 /dev/stdin /etc/sudoers.d/ext-core <<'EOS'
Defaults:ivan logfile=/var/log/ext-core-edit.log
ivan ALL=(ALL:ALL) NOPASSWD: sudoedit
EOS
  ext_core_gone_edit 'sudoedit -n foo'
  expect_rc 1
  expect_err_has 'sudoedit: foo: editing files in a writable directory is not permitted'
  run root 'cat /var/log/ext-core-edit.log'
  expect_out_has 'COMMAND=/usr/bin/true -- foo'
  rm -f /var/log/ext-core-edit.log
  end
}

begin ext-core-edit-relative-prompts-first && {
  install -m 0440 /dev/stdin /etc/sudoers.d/ext-core <<'EOS'
ivan ALL=(ALL:ALL) sudoedit
EOS
  ext_core_gone_edit 'echo ivanpw | sudoedit -S sub/foo'
  expect_rc 1
  expect_err_has '[sudo] password for ivan: sudoedit: sub/foo: No such file or directory'
  end
}

ext_core_raw_env() {
  cat >"$WORK/ext-core-raw.py" <<'PY'
import ctypes, sys
i = sys.argv.index("--")
env = [a.encode() for a in sys.argv[1:i]]
argv = [a.encode() for a in sys.argv[i + 1:]]
libc = ctypes.CDLL(None, use_errno=True)
libc.execve(argv[0], (ctypes.c_char_p * (len(argv) + 1))(*argv, None),
            (ctypes.c_char_p * (len(env) + 1))(*env, None))
sys.exit(127)
PY
  local user=$1 entry=$2
  shift 2
  run "$user" "python3 '$WORK/ext-core-raw.py' PATH=/usr/bin:/bin HOME=/tmp '$entry' -- /usr/bin/sudo $*"
}

ext_core_rebuild_fails() {
  expect_rc 1
  [[ $ERR == 'sudo: unable to rebuild the environment: Invalid argument' ]] ||
    fail 'stderr: expected only the rebuild failure'
  [[ -e /var/log/ext-core-env.log ]] && fail 'logfile: expected nothing logged'
}

begin ext-core-env-intake-edit-empty-name && {
  rm -f /var/log/ext-core-env.log
  printf 'original\n' >/tmp/ext-core-raw-file
  install -m 0440 /dev/stdin /etc/sudoers.d/ext-core <<'EOS'
Defaults logfile=/var/log/ext-core-env.log
ivan ALL=(ALL:ALL) NOPASSWD: ALL
EOS
  ext_core_raw_env ivan '=CF_EMPTY_NAME' -e /tmp/ext-core-raw-file
  ext_core_rebuild_fails
  ext_core_raw_env kate '=CF_EMPTY_NAME' -n -e /tmp/ext-core-raw-file
  ext_core_rebuild_fails
  rm -f /tmp/ext-core-raw-file /var/log/ext-core-env.log
  end
}

begin ext-core-env-intake-copy-modes && {
  rm -f /var/log/ext-core-env.log
  install -m 0440 /dev/stdin /etc/sudoers.d/ext-core <<'EOS'
Defaults logfile=/var/log/ext-core-env.log
Defaults:judy !env_reset
ivan ALL=(ALL:ALL) NOPASSWD: ALL
judy ALL=(ALL:ALL) NOPASSWD: ALL
EOS
  ext_core_raw_env ivan CF_NOEQUALS -E /usr/bin/true
  ext_core_rebuild_fails
  ext_core_raw_env judy CF_NOEQUALS /usr/bin/true
  ext_core_rebuild_fails
  ext_core_raw_env ivan CF_NOEQUALS /usr/bin/true
  expect_rc 0
  [[ -z $ERR ]] || fail 'stderr: expected empty with env_reset'
  rm -f /var/log/ext-core-env.log
  end
}

begin ext-core-env-intake-json-submitenv && {
  rm -f /var/log/ext-core-env.log
  install -m 0440 /dev/stdin /etc/sudoers.d/ext-core <<'EOS'
Defaults logfile=/var/log/ext-core-env.log, log_format=json_compact
ivan ALL=(ALL:ALL) NOPASSWD: ALL
EOS
  ext_core_raw_env ivan CF_NOEQUALS /usr/bin/true
  expect_rc 0
  run root 'cat /var/log/ext-core-env.log'
  expect_out_has '"submitenv":["PATH=/usr/bin:/bin","HOME=/tmp","CF_NOEQUALS"]'
  rm -f /var/log/ext-core-env.log
  end
}

begin ext-core-not-authenticate-passwd-deny-prompts && {
  install -m 0440 /dev/stdin /etc/sudoers.d/ext-core <<'EOS'
Defaults !authenticate, !lecture
ivan ALL=(ALL) ALL, PASSWD: !/usr/bin/id
EOS
  run ivan 'sudo -kS /usr/bin/id'
  expect_rc 1
  expect_err_has '[sudo] password for ivan:'
  run ivan 'printf "ivanpw\n" | sudo -kS /usr/bin/id'
  expect_rc 1
  expect_err_has 'Sorry, user ivan is not allowed to execute'
  run ivan 'sudo -kS /usr/bin/true'
  expect_rc 0
  end
}
