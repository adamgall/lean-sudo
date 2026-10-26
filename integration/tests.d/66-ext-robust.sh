
ext_robust_policy() {
  install -m 0440 /dev/stdin /etc/sudoers.d/ext-robust <<'EOF'
Defaults logfile=/var/log/ext-robust.log, loglinelen=0
kate ALL=(ALL:ALL) NOPASSWD: ALL
EOF
  rm -f /var/log/ext-robust.log
}

ext_robust_no_root() {
  cat >/etc/sudoers <<'EOF'
Defaults !mail_no_user
EOF
}

ext_robust_limits() {
  OUT=$(tr -s ' ' <<<"$OUT")
}

cat >"$WORK/ext-robust-fds.py" <<'PY'
import os
import sys
os.write(2, "".join(os.readlink("/proc/self/fd/%s" % fd) + "\n" for fd in sys.argv[1:]).encode())
PY
chmod 0644 "$WORK/ext-robust-fds.py"

ext_robust_fds() {
  run "$1" "sudo -n python3 $WORK/ext-robust-fds.py $2 $3"
}

begin ext-robust-closed-std-fd-reopened && {
  ext_robust_policy
  run root 'sudo -n readlink /proc/self/fd/0 0<&-'
  expect_rc 0
  expect_out_line /dev/null
  [[ -z $ERR ]] || fail 'stderr: expected empty'
  ext_robust_fds root 1 '1>&-'
  expect_rc 0
  [[ $ERR == /dev/null ]] || fail 'stderr: expected /dev/null'
  run root 'sudo -n readlink /proc/self/fd/2 2>&-'
  expect_rc 0
  expect_out_line /dev/null
  run kate 'sudo -n readlink /proc/self/fd/0 /proc/self/fd/2 0<&- 2>&-'
  expect_rc 0
  [[ $OUT == $'/dev/full\n/dev/null' ]] || fail 'stdout: expected the setuid-startup descriptors'
  end
}

begin ext-robust-two-closed-std-fds && {
  ext_robust_policy
  run root 'sudo -n readlink /proc/self/fd/0 /proc/self/fd/2 0<&- 2>&-'
  expect_rc 0
  [[ $OUT == $'/dev/null\n/dev/null' ]] || fail 'stdout: expected /dev/null twice'
  ext_robust_fds root '0 1' '0<&- 1>&-'
  expect_rc 0
  [[ $ERR == $'/dev/null\n/dev/null' ]] || fail 'stderr: expected /dev/null twice'
  end
}

begin ext-robust-two-closed-std-fds-denied && {
  ext_robust_no_root
  run root 'sudo -n true 0<&- 1>&-; echo rc=$? >&2'
  [[ $ERR == $'root is not in the sudoers file.\nrc=1' ]] ||
    fail 'stderr: expected the not-in-sudoers denial and rc=1'
  run root 'sudo -n true 0<&- 2>&-; echo rc=$?'
  expect_out_line rc=1
  end
}

begin ext-robust-rlimit-as-one-gib && {
  run root 'prlimit --as=1073741824 sudo -n grep "^Max address space" /proc/self/limits'
  ext_robust_limits
  expect_rc 0
  expect_out_line 'Max address space 1073741824 1073741824 bytes '
  [[ -z $ERR ]] || fail 'stderr: expected empty'
  ext_robust_no_root
  run root 'prlimit --fsize=4096 --nofile=24 --as=1073741824 sudo -n true'
  expect_rc 1
  [[ $ERR == 'root is not in the sudoers file.' ]] ||
    fail 'stderr: expected the not-in-sudoers denial'
  end
}

begin ext-robust-rlimit-nofile-small && {
  ext_robust_policy
  run kate 'prlimit --nofile=64:1024 sudo -n grep "^Max open files" /proc/self/limits'
  ext_robust_limits
  expect_rc 0
  expect_out_line 'Max open files 64 1024 files '
  [[ -z $ERR ]] || fail 'stderr: expected empty'
  run kate 'prlimit --nproc=64 --nofile=24 sudo -n grep -E "^Max (processes|open files)" /proc/self/limits'
  ext_robust_limits
  expect_rc 0
  [[ $OUT == $'Max processes 64 64 processes \nMax open files 24 24 files ' ]] ||
    fail 'stdout: expected restored limits'
  [[ -z $ERR ]] || fail 'stderr: expected empty'
  grep -q 'kate : PWD=/home/kate ; USER=root ; COMMAND=/usr/bin/grep -E' /var/log/ext-robust.log ||
    fail 'logfile: expected the command line'
  run root 'prlimit --nofile=24 sudo -n true'
  expect_rc 0
  [[ -z $ERR ]] || fail 'stderr: expected empty'
  end
}

begin ext-robust-deleted-cwd && {
  ext_robust_policy
  run kate 'mkdir -p gone && cd gone && rmdir ../gone && sudo -n readlink /proc/self/cwd'
  expect_rc 0
  expect_out_line '/home/kate/gone (deleted)'
  [[ -z $ERR ]] || fail 'stderr: expected empty'
  grep -qx '.* : kate : USER=root ; COMMAND=/usr/bin/readlink /proc/self/cwd' /var/log/ext-robust.log ||
    fail 'logfile: expected a command line without PWD='
  run kate 'mkdir -p gone && cd gone && rmdir ../gone && sudo -n -l'
  expect_rc 0
  expect_out_has '(ALL : ALL) NOPASSWD: ALL'
  run kate 'mkdir -p gone && cd gone && rmdir ../gone && sudo -n ./missing'
  expect_rc 1
  expect_err_has 'sudo: ./missing: command not found'
  run kate 'mkdir -p gone && cd gone && rmdir ../gone && sudo -n -i pwd'
  expect_rc 0
  expect_out_line /root
  grep -q 'kate : PWD=/root ; USER=root ; COMMAND=/bin/bash' /var/log/ext-robust.log ||
    fail 'logfile: expected PWD of the login shell'
  run kate 'mkdir -p gone && cd gone && rmdir ../gone && sudo -V'
  expect_rc 0
  expect_out_has 'Sudo version 1.9.17p2'
  end
}

begin ext-robust-deleted-cwd-json-log && {
  install -m 0440 /dev/stdin /etc/sudoers.d/ext-robust <<'EOF'
Defaults logfile=/var/log/ext-robust.log, log_format=json
kate ALL=(ALL:ALL) NOPASSWD: ALL
EOF
  rm -f /var/log/ext-robust.log
  run kate 'mkdir -p gone && cd gone && rmdir ../gone && sudo -n true'
  expect_rc 0
  grep -q '"command": "/usr/bin/true"' /var/log/ext-robust.log || fail 'logfile: expected a JSON accept record'
  ! grep -qE '"(submitcwd|runcwd)"' /var/log/ext-robust.log || fail 'logfile: expected no cwd fields'
  end
}

cat >"$WORK/ext-robust-signal.py" <<'PY'
import os
import signal
import subprocess
import sys
import time
user, name, delay = sys.argv[1], sys.argv[2], float(sys.argv[3])
marker = "/tmp/ext-robust-ran"
if os.path.exists(marker):
    os.unlink(marker)
process = subprocess.Popen(
    ["setpriv", "--reuid=" + user, "--regid=" + user, "--init-groups",
     "sudo", "-S", "touch", marker],
    stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
time.sleep(delay)
process.send_signal(getattr(signal, name))
time.sleep(1.5 - delay)
out, err = process.communicate((user + "pw\n").encode(), timeout=20)
sys.stdout.write("status=%d ran=%s\n" % (process.returncode, os.path.exists(marker)))
sys.stdout.write(err.decode())
PY

begin ext-robust-signal-before-prompt-acts-at-exec && {
  cp -a /etc/pam.d/sudo "$WORK/ext-robust-pam-sudo"
  sed -i 's|^@include common-auth|auth optional pam_exec.so /usr/bin/sleep 1\n&|' /etc/pam.d/sudo
  install -m 0440 /dev/stdin /etc/sudoers.d/ext-robust <<'EOF'
Defaults lecture=never
ivan ALL=(ALL:ALL) ALL
EOF
  for sig in SIGTERM SIGHUP SIGUSR1; do
    run root "python3 '$WORK/ext-robust-signal.py' ivan $sig 0.5"
    expect_rc 0
    num=$(python3 -c "import signal; print(int(signal.$sig))")
    expect_out_line "status=-$num ran=False"
    expect_out_line '[sudo] password for ivan: '
    expect_out_lacks 'password is required'
  done
  cp -a "$WORK/ext-robust-pam-sudo" /etc/pam.d/sudo
  end
}

cat >"$WORK/ext-robust-prompt-signal.py" <<'PY'
import os
import signal
import subprocess
import sys
user, name, password, order = sys.argv[1], sys.argv[2], sys.argv[3], sys.argv[4]
marker = "/tmp/ext-robust-ran"
if os.path.exists(marker):
    os.unlink(marker)
reader, writer = os.pipe()
process = subprocess.Popen(
    ["setpriv", "--reuid=" + user, "--regid=" + user, "--init-groups",
     "sudo", "-S", "-p", "pw: ", "touch", marker],
    stdin=reader, stderr=subprocess.PIPE)
os.close(reader)
prompt = b""
while not prompt.endswith(b"pw: "):
    prompt += process.stderr.read(1)
if order == "kill-first":
    process.send_signal(getattr(signal, name))
os.write(writer, (password + "\n").encode())
if order == "write-first":
    process.send_signal(getattr(signal, name))
os.close(writer)
rest = process.stderr.read().decode()
process.wait()
sys.stdout.write("status=%d ran=%s\n" % (process.returncode, os.path.exists(marker)))
sys.stdout.write(rest)
PY

begin ext-robust-signal-during-stdin-password-read && {
  install -m 0440 /dev/stdin /etc/sudoers.d/ext-robust <<'EOF'
Defaults lecture=never, passwd_tries=2
ivan ALL=(ALL:ALL) ALL
EOF
  for sig in SIGINT SIGQUIT SIGHUP; do
    num=$(python3 -c "import signal; print(int(signal.$sig))")
    for order in kill-first write-first; do
      reset_state
      install -m 0440 /dev/stdin /etc/sudoers.d/ext-robust <<'EOF'
Defaults lecture=never, passwd_tries=2
ivan ALL=(ALL:ALL) ALL
EOF
      run root "python3 '$WORK/ext-robust-prompt-signal.py' ivan $sig ivanpw $order"
      expect_rc 0
      expect_out_line "status=-$num ran=False"
      expect_out_lacks 'password is required'
      run root "python3 '$WORK/ext-robust-prompt-signal.py' ivan $sig wrong $order"
      expect_rc 0
      expect_out_line 'status=1 ran=False'
      expect_out_line 'Sorry, try again.'
      expect_out_line 'sudo: no password was provided'
      expect_out_line 'sudo: 1 incorrect password attempt'
    done
  done
  end
}
