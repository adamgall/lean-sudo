
cat >"$WORK/ext-auth-tty.py" <<'PY'
import os
import pty
import pwd
import select
import signal
import sys
import time

mode, user, answer = sys.argv[1], sys.argv[2], sys.argv[3]
pw = pwd.getpwnam(user)
env = {
    "HOME": pw.pw_dir, "USER": pw.pw_name, "LOGNAME": pw.pw_name, "SHELL": "/bin/sh",
    "PATH": "/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin",
    "TERM": "dumb", "LANG": "C.UTF-8",
}
reader, writer = os.pipe()
pid, fd = pty.fork()
if pid == 0:
    try:
        os.dup2(writer, 2)
        os.close(reader)
        os.close(writer)
        os.initgroups(pw.pw_name, pw.pw_gid)
        os.setgid(pw.pw_gid)
        os.setuid(pw.pw_uid)
        os.chdir(pw.pw_dir)
        if mode == "wrapper-close":
            argv = ["sh", "-c", "trap 'echo sh-saw-SIGHUP >&2' HUP; "
                    "sudo -k /usr/bin/true; echo sudo-exit=$? >&2"]
        else:
            argv = ["sudo", "-k", "/usr/bin/true"]
        os.execvpe(argv[0], argv, env)
    finally:
        os._exit(127)
os.close(writer)
transcript = bytearray()


def pump():
    try:
        data = os.read(fd, 4096)
    except OSError:
        data = b""
    transcript.extend(data)
    return bool(data)


def prompts(count):
    deadline = time.monotonic() + 30
    while transcript.count(b"password for") < count:
        left = deadline - time.monotonic()
        if left <= 0 or not select.select([fd], [], [], left)[0] or not pump():
            sys.exit("prompt %d not seen" % count)


prompts(1)
time.sleep(0.2)
os.write(fd, answer.encode() + b"\n")
prompts(2)
time.sleep(0.2)
if mode == "leader-kill":
    os.kill(pid, signal.SIGHUP)
    while pump():
        pass
else:
    os.close(fd)
errors = bytearray()
while True:
    chunk = os.read(reader, 4096)
    if not chunk:
        break
    errors.extend(chunk)
_, status = os.waitpid(pid, 0)
code = os.WEXITSTATUS(status) if os.WIFEXITED(status) else 128 + os.WTERMSIG(status)
print("rc=%d" % code)
if mode == "leader-kill":
    sys.stdout.write(transcript.decode("utf-8", "replace").replace("\r", ""))
sys.stderr.write(errors.decode("utf-8", "replace"))
PY

cat >"$WORK/ext-auth-signal.py" <<'PY'
import os
import pwd
import select
import signal
import subprocess
import sys
import time

user, name = sys.argv[1], sys.argv[2]
before, after = (value.encode().decode("unicode_escape") for value in sys.argv[3:5])
pw = pwd.getpwnam(user)
env = {
    "HOME": pw.pw_dir, "USER": pw.pw_name, "LOGNAME": pw.pw_name, "SHELL": "/bin/sh",
    "PATH": "/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin", "LANG": "C.UTF-8",
}


def become():
    os.initgroups(pw.pw_name, pw.pw_gid)
    os.setgid(pw.pw_gid)
    os.setuid(pw.pw_uid)
    os.chdir(pw.pw_dir)


child = subprocess.Popen(["sudo", "-S", "-k", "/usr/bin/true"], stdin=subprocess.PIPE,
                         stderr=subprocess.PIPE, env=env, preexec_fn=become)
errors = bytearray()


def prompts(count):
    deadline = time.monotonic() + 20
    while errors.count(b"password for") < count:
        left = deadline - time.monotonic()
        if left <= 0 or not select.select([child.stderr], [], [], left)[0]:
            sys.exit("prompt %d not seen" % count)
        chunk = os.read(child.stderr.fileno(), 4096)
        if not chunk:
            sys.exit("prompt %d not seen" % count)
        errors.extend(chunk)


prompts(1)
if before:
    child.stdin.write(before.encode())
    child.stdin.flush()
    prompts(2)
time.sleep(0.3)
child.send_signal(getattr(signal, name))
time.sleep(0.3)
try:
    child.stdin.write(after.encode())
    child.stdin.close()
except OSError:
    pass
errors.extend(child.stderr.read())
code = child.wait()
print("rc=%d" % (code if code >= 0 else 128 - code))
sys.stderr.write(errors.decode("utf-8", "replace"))
PY

cat >"$WORK/ext-auth-job.py" <<'PY'
import os
import pwd
import re
import select
import signal
import subprocess
import sys
import time

mode, user, password = sys.argv[1], sys.argv[2], sys.argv[3]
pw = pwd.getpwnam(user)
env = {
    "HOME": pw.pw_dir, "USER": pw.pw_name, "LOGNAME": pw.pw_name, "SHELL": "/bin/sh",
    "PATH": "/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin", "LANG": "C.UTF-8",
}


def become():
    if mode != "orphan":
        os.setpgid(0, 0)
    os.initgroups(pw.pw_name, pw.pw_gid)
    os.setgid(pw.pw_gid)
    os.setuid(pw.pw_uid)
    os.chdir(pw.pw_dir)


child = subprocess.Popen(["sudo", "-S"] + sys.argv[4:], stdin=subprocess.PIPE,
                         stderr=subprocess.PIPE, env=env, preexec_fn=become,
                         start_new_session=mode == "orphan")
errors = bytearray()


def threads():
    found = []
    for task in os.listdir("/proc/%d/task" % child.pid):
        try:
            with open("/proc/%d/task/%s/stat" % (child.pid, task)) as stream:
                state = stream.read().rsplit(")", 1)[1].split()[0]
            with open("/proc/%d/task/%s/wchan" % (child.pid, task)) as stream:
                found.append((state, stream.read()))
        except OSError:
            pass
    return found


def reading():
    return any(re.search(r"pipe_read$|(^|_)p?poll$", wchan) for _, wchan in threads())


def stopped():
    return all(state == "T" for state, _ in threads())


def await_state(predicate, what):
    deadline = time.monotonic() + 20
    while not predicate():
        if time.monotonic() > deadline:
            sys.exit("%s not reached" % what)
        if select.select([child.stderr], [], [], 0.01)[0]:
            chunk = os.read(child.stderr.fileno(), 4096)
            if not chunk:
                sys.exit("%s not reached" % what)
            errors.extend(chunk)


await_state(lambda: b"password for" in errors and reading(), "prompt read")
if mode == "stop-term":
    child.send_signal(signal.SIGSTOP)
    await_state(stopped, "stop")
    child.send_signal(signal.SIGTERM)
    child.stdin.write(password.encode() + b"\n")
    child.stdin.flush()
    child.send_signal(signal.SIGCONT)
else:
    child.send_signal(signal.SIGTSTP)
    if mode == "stop":
        await_state(stopped, "stop")
        child.send_signal(signal.SIGCONT)
    else:
        await_state(lambda: b"\n" in errors, "interruption")
try:
    child.stdin.write(password.encode() + b"\n")
    child.stdin.close()
except OSError:
    pass
errors.extend(child.stderr.read())
code = child.wait()
print("rc=%d" % (code if code >= 0 else 128 - code))
sys.stderr.write(errors.decode("utf-8", "replace"))
PY

ext_auth_sudoers() {
  install -m 0440 /dev/stdin /etc/sudoers.d/ext-auth <<'EOF'
ivan ALL=(ALL:ALL) ALL
EOF
}

ext_auth_expect_err() {
  [[ $ERR == "$1" ]] || fail "stderr: expected exactly '$1'"
}

begin ext-auth-stdin-eof-newline && {
  ext_auth_sudoers
  eof=$'[sudo] password for ivan: \nsudo: no password was provided\nsudo: a password is required'
  for cmd in 'sudo -S -k /usr/bin/true' 'printf "" | sudo -S -k /usr/bin/true' 'sudo -S -k -v'; do
    run ivan "$cmd"
    expect_rc 1
    expect_out_empty
    ext_auth_expect_err "$eof"
  done
  run ivan "printf 'wrong\n' | sudo -S -k /usr/bin/true"
  expect_rc 1
  want=$'[sudo] password for ivan: Sorry, try again.\n[sudo] password for ivan: \n'
  want+=$'sudo: no password was provided\nsudo: 1 incorrect password attempt'
  ext_auth_expect_err "$want"
  run ivan "printf 'ivanpw\n' | sudo -S -k /usr/bin/true"
  expect_rc 0
  ext_auth_expect_err '[sudo] password for ivan: '
  end
}

begin ext-auth-stdin-bounded-reads && {
  ext_auth_sudoers
  prompt='[sudo] password for ivan: '
  sorry="${prompt}Sorry, try again."$'\n'
  eof=$'\nsudo: no password was provided\nsudo: '
  run ivan "head -c 1023 /dev/zero | tr '\\0' a | sudo -S -k /usr/bin/true"
  expect_rc 1
  ext_auth_expect_err "$sorry$prompt${eof}1 incorrect password attempt"
  run ivan "head -c 1024 /dev/zero | tr '\\0' a | sudo -S -k /usr/bin/true"
  expect_rc 1
  ext_auth_expect_err "$sorry$sorry$prompt${eof}2 incorrect password attempts"
  run ivan "head -c 2047 /dev/zero | tr '\\0' a | sudo -S -k /usr/bin/true"
  expect_rc 1
  ext_auth_expect_err "$sorry$sorry${prompt}sudo: 3 incorrect password attempts"
  run ivan "{ head -c 1023 /dev/zero | tr '\\0' a; printf 'ivanpw\n'; } | sudo -S -k /usr/bin/true"
  expect_rc 0
  ext_auth_expect_err "$sorry$prompt"
  run ivan "printf 'ivanpw\r\n' | sudo -S -k /usr/bin/true"
  expect_rc 0
  ext_auth_expect_err "$prompt"
  end
}

begin ext-auth-askpass-exec-failure && {
  ext_auth_sudoers
  install -m 0000 /dev/null /tmp/ext-auth-askpass
  tail=$'\nsudo: no password was provided\nsudo: a password is required'
  run ivan 'SUDO_ASKPASS=/nonexistent/askpass sudo -A -k /usr/bin/true'
  expect_rc 1
  ext_auth_expect_err "sudo: unable to run /nonexistent/askpass: No such file or directory$tail"
  run ivan 'SUDO_ASKPASS=/tmp/ext-auth-askpass sudo -A -k /usr/bin/true'
  expect_rc 1
  ext_auth_expect_err "sudo: unable to run /tmp/ext-auth-askpass: Permission denied$tail"
  run ivan 'SUDO_ASKPASS=ext-auth-askpass sudo -A -k /usr/bin/true'
  expect_rc 1
  ext_auth_expect_err "sudo: unable to run ext-auth-askpass: No such file or directory$tail"
  rm -f /tmp/ext-auth-askpass
  end
}

begin ext-auth-tty-hangup-session-leader && {
  ext_auth_sudoers
  restore=$'sudo: unable to restore terminal settings: Illegal seek\n'
  for answer in wrong "$(head -c 513 /dev/zero | tr '\0' a)"; do
    run root "python3 '$WORK/ext-auth-tty.py' leader-close ivan '$answer'"
    expect_out_line 'rc=1'
    ext_auth_expect_err "${restore}sudo: 1 incorrect password attempt"
  done
  end
}

begin ext-auth-tty-hangup-wrapper && {
  ext_auth_sudoers
  run root "python3 '$WORK/ext-auth-tty.py' wrapper-close ivan wrong"
  want=$'sudo: unable to restore terminal settings: Illegal seek\n'
  want+=$'sudo: 1 incorrect password attempt\nsh-saw-SIGHUP\nsudo-exit=1'
  ext_auth_expect_err "$want"
  end
}

begin ext-auth-tty-sighup-during-prompt && {
  ext_auth_sudoers
  run root "python3 '$WORK/ext-auth-tty.py' leader-kill ivan wrong"
  want=$'rc=1\n[sudo] password for ivan: \nSorry, try again.\n[sudo] password for ivan: '
  [[ $OUT == "$want" ]] || fail "stdout: expected exactly '$want'"
  ext_auth_expect_err 'sudo: 1 incorrect password attempt'
  end
}

begin ext-auth-pam-group-setcred && {
  cp -a /etc/pam.d/sudo "$WORK/ext-auth-pam-sudo"
  cp -a /etc/security/group.conf "$WORK/ext-auth-group-conf"
  groupadd ext-pamgrp
  ext_auth_sudoers
  cat >/etc/pam.d/sudo <<'EOF'
auth optional pam_group.so
auth sufficient pam_unix.so nullok
auth requisite pam_deny.so
EOF
  printf '*;*;*;Al0000-2400;ext-pamgrp\n' >/etc/security/group.conf
  run root 'sudo -u ivan -- id -Gn'
  expect_rc 0
  expect_out_line "$(id -Gn ivan) ext-pamgrp"
  run root 'sudo -- id -Gn'
  expect_rc 0
  expect_out_line 'root ext-pamgrp'
  run ivan "printf 'ivanpw\n' | sudo -S -k -- id -Gn"
  expect_rc 0
  expect_out_line 'root ext-pamgrp'
  printf 'Defaults !pam_setcred\n' >>/etc/sudoers.d/ext-auth
  run root 'sudo -u ivan -- id -Gn'
  expect_rc 0
  expect_out_line "$(id -Gn ivan)"
  cp -a "$WORK/ext-auth-pam-sudo" /etc/pam.d/sudo
  cp -a "$WORK/ext-auth-group-conf" /etc/security/group.conf
  groupdel ext-pamgrp
  end
}

begin ext-auth-stdin-signal-at-prompt && {
  ext_auth_sudoers
  prompt='[sudo] password for ivan: '
  for sig in SIGINT SIGQUIT SIGTERM SIGHUP; do
    run root "python3 '$WORK/ext-auth-signal.py' ivan $sig '' 'ivanpw\\n'"
    expect_out_line 'rc=1'
    ext_auth_expect_err "$prompt"$'\nsudo: a password is required'
    run root "python3 '$WORK/ext-auth-signal.py' ivan $sig 'wrong\\n' 'ivanpw\\n'"
    expect_out_line 'rc=1'
    want="${prompt}Sorry, try again."$'\n'"$prompt"$'\nsudo: 1 incorrect password attempt'
    ext_auth_expect_err "$want"
  done
  end
}

begin ext-auth-stdin-signal-buffered-input && {
  ext_auth_sudoers
  run root "python3 '$WORK/ext-auth-job.py' stop-term ivan ivanpw -k /usr/bin/true"
  expect_out_line 'rc=1'
  ext_auth_expect_err $'[sudo] password for ivan: \nsudo: a password is required'
  end
}

begin ext-auth-stdin-suspend-at-prompt && {
  ext_auth_sudoers
  prompt='[sudo] password for ivan: '
  ts=/run/sudo/ts/$(uid_of ivan)
  for mode in stop orphan; do
    rm -rf /run/sudo
    run root "python3 '$WORK/ext-auth-job.py' $mode ivan ivanpw -k /usr/bin/true"
    expect_out_line 'rc=0'
    ext_auth_expect_err "$prompt"$'\n'"$prompt"
    [[ -s $ts ]] || fail "$mode: resuming must reopen and lock the time stamp file"
    rm -rf /run/sudo
    run root "python3 '$WORK/ext-auth-job.py' $mode ivan ivanpw /usr/bin/true"
    expect_out_line 'rc=0'
    ext_auth_expect_err "$prompt"$'\n'"$prompt"
  done
  printf 'Defaults:ivan timestamp_timeout=0\n' >>/etc/sudoers.d/ext-auth
  for mode in stop orphan; do
    rm -rf /run/sudo
    run root "python3 '$WORK/ext-auth-job.py' $mode ivan ivanpw /usr/bin/true"
    expect_out_line 'rc=1'
    ext_auth_expect_err "$prompt"$'\nsudo: a password is required'
    [[ ! -e $ts ]] || fail "$mode: a zero timeout must not create a time stamp file"
  done
  end
}

begin ext-auth-tty-suspend-at-prompt && {
  ext_auth_sudoers
  pty ivan 'PS1="OUTER> " /bin/bash --norc -i' -e 'OUTER> ' -s 'sudo -k /usr/bin/id -u\r' \
    -e 'password for ivan: ' -s $'\032' -e 'Stopped' -e 'OUTER> ' -s 'fg\r' \
    -e 'password for ivan: ' -s 'ivanpw\r' -e '\r\n0\r\n' -e 'OUTER> ' -s 'exit\r'
  expect_rc 0
  [[ $OUT == *$'[sudo] password for ivan: \n\n[1]+  Stopped'* ]] ||
    fail 'transcript: expected a newline before the stop'
  [[ $OUT == *$'OUTER> fg\nsudo -k /usr/bin/id -u\n[sudo] password for ivan: \n0\n'* ]] ||
    fail 'transcript: expected a fresh prompt after resuming'
  end
}

begin ext-auth-pam-session-umask && {
  install -m 0440 /dev/stdin /etc/sudoers.d/ext-auth <<'EOF'
ivan ALL=(ALL:ALL) NOPASSWD: ALL
EOF
  run ivan "sudo -u judy /bin/sh -c umask; sudo /bin/sh -c umask; sudo -u judy -g judy /bin/sh -c umask"
  expect_rc 0
  [[ $OUT == $'0002\n0022\n0002' ]] || fail "stdout: expected pam_umask results, got '$OUT'"
  printf 'Defaults:judy umask=0022\n' >>/etc/sudoers.d/ext-auth
  run ivan "sudo -u judy /bin/sh -c umask; sudo /bin/sh -c umask"
  expect_rc 0
  [[ $OUT == $'0002\n0022' ]] || fail "stdout: expected a non-matching umask default to stay inactive, got '$OUT'"
  printf 'Defaults umask=0022\n' >>/etc/sudoers.d/ext-auth
  run ivan "sudo -u judy /bin/sh -c umask; sudo -u judy -g judy /bin/sh -c umask"
  expect_rc 0
  [[ $OUT == $'0022\n0022' ]] || fail "stdout: expected explicit sudoers umask to win, got '$OUT'"
  printf 'Defaults umask=0077, umask_override\n' >>/etc/sudoers.d/ext-auth
  run ivan "sudo -u judy /bin/sh -c umask; sudo /bin/sh -c umask"
  expect_rc 0
  [[ $OUT == $'0077\n0077' ]] || fail "stdout: expected umask_override to win, got '$OUT'"
  end
}

begin ext-auth-stdin-unusable-descriptors && {
  install -m 0440 /dev/stdin /etc/sudoers.d/ext-auth <<'EOT'
Defaults:ivan passwd_tries=1, logfile=/tmp/ext-auth.log
ivan ALL=(ALL:ALL) ALL
EOT
  rm -f /tmp/ext-auth.log
  run ivan 'sudo -S -k /usr/bin/true 0>/dev/null'
  expect_rc 1
  want=$'[sudo] password for ivan: \nsudo: unable to read password: Bad file descriptor\n'
  ext_auth_expect_err "${want}sudo: a password is required"
  rm -f /tmp/ext-auth.log
  run ivan "printf 'wrong\n' | sudo -S -k /usr/bin/true 2</dev/null"
  expect_rc 1
  ! grep -qF 'incorrect password attempt' /tmp/ext-auth.log 2>/dev/null ||
    fail 'logfile: a failed prompt write must not count a password attempt'
  rm -f /tmp/ext-auth.log
  end
}
