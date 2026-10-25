
begin background-syslog-exit && {
  python3 - >"$WORK/background-syslog" 2>&1 <<'PY' || fail "$(cat "$WORK/background-syslog")"
import os
import pathlib
import pwd
import re
import subprocess
import sys
import tempfile

sys.path.insert(0, '/usr/local/lib')
from sudo_it_logging import Syslog

policy = pathlib.Path('/etc/sudoers.d/background-syslog')
policy.write_text('Defaults log_exit_status,syslog_pid,!use_pty\n'
                  'ivan ALL=(ALL:ALL) NOPASSWD: ALL\n')
policy.chmod(0o440)
user = pwd.getpwnam('ivan')
env = dict(HOME=user.pw_dir, USER='ivan', LOGNAME='ivan', SHELL='/bin/bash',
           PATH='/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin', LANG='C')

with tempfile.TemporaryDirectory(prefix='sudo-background-') as directory:
    os.chown(directory, user.pw_uid, user.pw_gid)
    child = pathlib.Path(directory) / 'supervisor'
    command = 'printf "%s\\n" "$PPID" > ' + str(child) + '; exit 7'

    def execute(binary):
        child.unlink(missing_ok=True)
        with Syslog() as logger:
            args = ['setpriv', '--reuid=' + str(user.pw_uid),
                    '--regid=' + str(user.pw_gid), '--init-groups', '--',
                    binary, '-n', '-b', '/bin/sh', '-c', command]
            result = subprocess.Popen(args, cwd=user.pw_dir, env=env,
                                      stdout=subprocess.PIPE, stderr=subprocess.PIPE)
            output, error = result.communicate(timeout=15)
            assert result.returncode == 0, (result.returncode, output, error)
            assert output == b'' and error == b'', (output, error)
            logger.wait(lambda: child.exists() and child.stat().st_size > 0)
            supervisor = int(child.read_text())
            logger.wait(lambda: any(' ; EXIT=7' in msg for msg in logger.messages()))
            records = []
            for message in logger.messages():
                match = re.search(r'sudo\[(\d+)\]:\s+(.*)', message)
                if match and 'COMMAND=' in match[2]:
                    records.append((int(match[1]), match[2]))
        assert len(records) == 2, records
        assert records[0][0] == result.pid, (records, result.pid)
        assert records[1][0] == supervisor != result.pid, (records, supervisor, result.pid)
        assert records[1][1] == records[0][1] + ' ; EXIT=7', records
        return [text for _, text in records]

    reference = execute('/usr/bin/sudo.ws')
    actual = execute('/usr/bin/sudo')
    assert actual == reference, (reference, actual)
PY
  end
}

begin exec-default-core-limit && {
  run root "ulimit -c unlimited; sudo -n /bin/sh -c 'ulimit -c; ulimit -Hc'"
  expect_rc 0
  expect_out_line 0
  [[ $OUT == $'0\n0' ]] || fail 'both command core limits must be zero'
  end
}

begin exec-configured-resource-limits && {
  install -m 0440 /dev/stdin /etc/sudoers.d/exec-limits <<'EOF'
Defaults rlimit_core="1024,2048", rlimit_nofile="128,256"
EOF
  run root "sudo -n /bin/bash -c 'ulimit -Sc; ulimit -Hc; ulimit -Sn; ulimit -Hn'"
  expect_rc 0
  [[ $OUT == $'1\n2\n128\n256' ]] || fail "unexpected limits: $OUT"
  end
}

begin exec-closed-standard-input && {
  run root "sudo -n /usr/bin/readlink /proc/self/fd/0 <&-"
  expect_rc 0
  expect_out_line /dev/null
  end
}

begin exec-login-missing-home && {
  oldhome=$(getent passwd ivan | cut -d: -f6)
  usermod -d /nonexistent-lean-sudo-home ivan
  run root "cd /tmp; sudo -n -i -u ivan /bin/echo login-continued"
  usermod -d "$oldhome" ivan
  expect_rc 0
  expect_out_line login-continued
  expect_err_has 'unable to change directory to /nonexistent-lean-sudo-home'
  end
}

begin exec-required-cwd-missing && {
  install -m 0440 /dev/stdin /etc/sudoers.d/exec-cwd <<'EOF'
root ALL = CWD=/nonexistent-lean-sudo-cwd NOPASSWD: ALL
EOF
  run root "sudo -n /bin/echo must-not-run"
  expect_rc_not 0
  expect_out_lacks must-not-run
  expect_err_has 'unable to change directory'
  end
}

begin exec-noexec-blocks-subcommand && {
  install -m 0440 /dev/stdin /etc/sudoers.d/exec-noexec <<'EOF'
root ALL = NOEXEC: NOPASSWD: ALL
EOF
  run root "sudo -n /bin/sh -c '/usr/bin/id; echo shell-survived'"
  expect_rc 0
  expect_out_line shell-survived
  expect_out_lacks 'uid='
  expect_err_has 'Permission denied'
  end
}

begin exec-command-timeout && {
  install -m 0440 /dev/stdin /etc/sudoers.d/exec-timeout <<'EOF'
root ALL = TIMEOUT=1 NOPASSWD: ALL
EOF
  start=$SECONDS
  run root "sudo -n /bin/sleep 10"
  expect_rc_not 0
  [[ $((SECONDS - start)) -lt 6 ]] || fail 'command timeout did not terminate promptly'
  end
}

begin exec-background-process-group && {
  marker=/tmp/lean-sudo-exec-background
  rm -f "$marker"
  run root "ps -o pgid= -p \$\$; sudo -n -b /bin/sh -c 'ps -o pgid= -p \$\$ >$marker; sleep 1' >/dev/null 2>&1; echo returned"
  expect_rc 0
  expect_out_line returned
  for _ in $(seq 1 30); do [[ -s $marker ]] && break; sleep .1; done
  [[ -s $marker ]] || fail 'background command did not run'
  caller_pgid=$(printf '%s\n' "$OUT" | tr -d ' ' | grep -E '^[0-9]+$')
  child_pgid=$(tr -d ' \n' <"$marker")
  [[ $caller_pgid != "$child_pgid" ]] || fail 'background command remained in caller process group'
  rm -f "$marker"
  end
}

begin exec-background-pty && {
  marker=/tmp/lean-sudo-exec-background-tty
  rm -f "$marker"
  pty root "tty; sudo -n -b /bin/sh -c 'tty >$marker'; sleep 1; cat $marker"
  expect_rc 0
  expect_out_has /dev/pts/
  [[ $(printf '%s' "$OUT" | grep -o '/dev/pts/[0-9]*' | sort -u | wc -l) -eq 1 ]] ||
    fail 'background command unexpectedly changed terminal'
  rm -f "$marker"
  end
}

begin exec-nproc-uid-switch && {
  run root "/bin/bash -c 'ulimit -u 1; exec sudo -n -u nobody /usr/bin/true'"
  expect_rc 0
  end
}

begin exec-apparmor-unknown-profile && {
  install -m 0440 /dev/stdin /etc/sudoers.d/exec-apparmor <<'EOF'
root ALL = APPARMOR_PROFILE=lean-sudo-nonexistent-profile NOPASSWD: ALL
EOF
  run root "sudo -n /bin/echo must-not-run"
  if [[ $(cat /sys/module/apparmor/parameters/enabled 2>/dev/null) == Y ]]; then
    expect_rc_not 0
    expect_out_lacks must-not-run
  else
    expect_rc 0
    expect_out_line must-not-run
  fi
  end
}

begin exec-timeout-escalates-to-kill && {
  install -m 0440 /dev/stdin /etc/sudoers.d/exec-timeout <<'EOF'
Defaults command_timeout=1
EOF
  start=$SECONDS
  run root "sudo -n /bin/sh -c 'trap \"\" HUP TERM; while :; do :; done'"
  expect_rc 137
  [[ $((SECONDS - start)) -lt 7 ]] || fail 'timeout did not escalate to SIGKILL'
  end
}

begin exec-preserve-user-core-limit && {
  install -m 0440 /dev/stdin /etc/sudoers.d/exec-limits <<'EOF'
Defaults rlimit_core=user
EOF
  run root "/bin/bash -c 'ulimit -Sc 42; exec sudo -n /bin/bash -c \"ulimit -Sc\"'"
  expect_rc 0
  expect_out_line 42
  end
}

begin exec-noexec-preload-order && {
  install -m 0440 /dev/stdin /etc/sudoers.d/exec-noexec <<'EOF'
root ALL = NOEXEC: NOPASSWD: ALL
EOF
  run root "sudo -n LD_PRELOAD=/nonexistent-noexec-test.so /usr/bin/env"
  expect_rc 0
  expect_out_line 'LD_PRELOAD=/usr/libexec/sudo/sudo_noexec.so:/nonexistent-noexec-test.so'
  end
}

begin exec-unlimited-core-limit && {
  install -m 0440 /dev/stdin /etc/sudoers.d/exec-limits <<'EOF'
Defaults rlimit_core=infinity
EOF
  run root "sudo -n /bin/bash -c 'ulimit -Sc'"
  expect_rc 0
  expect_out_line unlimited
  end
}

begin exec-disabled-core-limit-override && {
  install -m 0440 /dev/stdin /etc/sudoers.d/exec-limits <<'EOF'
Defaults !rlimit_core
EOF
  run root "/bin/bash -c 'ulimit -Sc 42; exec sudo -n /bin/bash -c \"ulimit -Sc\"'"
  expect_rc 0
  expect_out_line 0
  end
}

begin exec-disabled-core-limit-without-pam-session && {
  install -m 0440 /dev/stdin /etc/sudoers.d/exec-limits <<'EOF'
Defaults !rlimit_core,!pam_session
EOF
  run root "/bin/bash -c 'ulimit -Sc 42; exec sudo -n /bin/bash -c \"ulimit -Sc\"'"
  expect_rc 0
  expect_out_line 42
  end
}

begin exec-disabled-core-limit-pam-override && {
  printf 'root soft core 7\n' >/etc/security/limits.d/99-sudo-it-core.conf
  install -m 0440 /dev/stdin /etc/sudoers.d/exec-limits <<'EOF'
Defaults !rlimit_core
EOF
  run root "/bin/bash -c 'ulimit -Sc 42; exec sudo -n /bin/bash -c \"ulimit -Sc\"'"
  expect_rc 0
  expect_out_line 7
  rm -f /etc/sudoers.d/exec-limits
  install -m 0440 /dev/stdin /etc/sudoers.d/exec-limits <<'EOF'
Defaults rlimit_core="1024,2048"
EOF
  run root "sudo -n /bin/bash -c 'ulimit -Sc; ulimit -Hc'"
  expect_rc 0
  [[ $OUT == $'1\n2' ]] || fail "sudoers core limit did not override PAM: $OUT"
  rm -f /etc/security/limits.d/99-sudo-it-core.conf
  end
}

begin exec-pty-utmp-session && {
  install -m 0664 /dev/null /run/utmp
  install -m 0440 /dev/stdin /etc/sudoers.d/exec-utmp <<'EOF'
Defaults use_pty, set_utmp, utmp_runas
EOF

  pty root "sudo -n -u ivan /usr/bin/python3 -c 'print(\"ivan\" if b\"ivan\" in open(\"/run/utmp\", \"rb\").read() else \"missing\")'"
  expect_rc 0
  expect_out_has ivan
  run root "python3 -c 'print(\"ivan\" if b\"ivan\" in open(\"/run/utmp\", \"rb\").read() else \"cleared\")'"
  expect_rc 0
  expect_out_lacks ivan
  end
}

begin exec-initial-background-tty-resume && {
  install -m 0440 /dev/stdin /etc/sudoers.d/exec-background <<'EOF'
Defaults use_pty, exec_background
EOF
  pty root "sudo -n /usr/bin/python3 -c 'import os; print(\"initial-background=\" + str(os.tcgetpgrp(0) != os.getpgrp()), flush=True); input(); print(\"resumed-foreground=\" + str(os.tcgetpgrp(0) == os.getpgrp()))'" \
    -e 'initial-background=True' -s 'continue\r'
  expect_rc 0
  expect_out_has initial-background=True
  expect_out_has resumed-foreground=True
  end
}

begin exec-nopty-timeout-signals-only-command && {
  install -m 0440 /dev/stdin /etc/sudoers.d/exec-timeout <<'EOF'
Defaults !use_pty
root ALL = TIMEOUT=2 NOPASSWD: /bin/sh
EOF
  marker="$WORK/timeout-descendant"


  run root "sudo -n /bin/sh -c '/bin/sleep 30 & echo \$! >\"$marker\"; wait'"
  expect_rc_not 0
  sleep_pid=$(cat "$marker" 2>/dev/null)
  if [[ $sleep_pid =~ ^[0-9]+$ ]] && [[ -r /proc/$sleep_pid/stat ]]; then
    state=$(ps -o stat= -p "$sleep_pid")
    [[ -n $state && $state != Z* ]] || fail 'non-pty timeout killed the background descendant'
    kill "$sleep_pid" 2>/dev/null || :
  else
    fail 'background descendant did not survive non-pty command timeout'
  fi
  rm -f "$marker"
  end
}

begin exec-stay-setuid-root-invoker && {
  install -m 0440 /dev/stdin /etc/sudoers.d/exec-stay-setuid <<'EOF'
Defaults stay_setuid
EOF
  bob_uid=$(id -u bob)
  run root "sudo -n -u bob /usr/bin/python3 -c 'import os; print(\"uid\", os.getresuid()); print(\"gid\", os.getresgid())'"
  expect_rc 0
  expect_out_line "uid (0, $bob_uid, $bob_uid)"
  expect_out_line "gid (0, 0, 0)"
  end
}

begin exec-stay-setuid-nonroot-invoker && {
  install -m 0440 /dev/stdin /etc/sudoers.d/exec-stay-setuid <<'EOF'
Defaults stay_setuid
ivan ALL = (ALL:ALL) NOPASSWD: ALL
EOF
  ivan_uid=$(id -u ivan); ivan_gid=$(id -g ivan)
  bob_uid=$(id -u bob)
  run ivan "sudo -n -u bob -g daemon /usr/bin/python3 -c 'import os; print(\"uid\", os.getresuid()); print(\"gid\", os.getresgid()); print(os.environ[\"USER\"]); print(os.environ[\"SUDO_UID\"])'"
  expect_rc 0
  expect_out_line "uid ($ivan_uid, $bob_uid, $bob_uid)"
  expect_out_line "gid ($ivan_gid, $ivan_gid, $ivan_gid)"
  expect_out_line bob
  expect_out_line "$ivan_uid"
  end
}

begin exec-stay-setuid-root-target && {
  install -m 0440 /dev/stdin /etc/sudoers.d/exec-stay-setuid <<'EOF'
Defaults stay_setuid, use_pty
ivan ALL = (ALL) NOPASSWD: ALL
EOF
  ivan_uid=$(id -u ivan); ivan_gid=$(id -g ivan)
  pty ivan "sudo -n /usr/bin/python3 -c 'import os; print(\"uid\", os.getresuid()); print(\"gid\", os.getresgid())'"
  expect_rc 0
  expect_out_has "uid ($ivan_uid, 0, 0)"
  expect_out_has "gid ($ivan_gid, $ivan_gid, $ivan_gid)"
  end
}

begin exec-stay-setuid-disabled && {
  install -m 0440 /dev/stdin /etc/sudoers.d/exec-stay-setuid <<'EOF'
Defaults !stay_setuid
EOF
  bob_uid=$(id -u bob); bob_gid=$(id -g bob)
  run root "sudo -n -u bob /usr/bin/python3 -c 'import os; print(\"uid\", os.getresuid()); print(\"gid\", os.getresgid())'"
  expect_rc 0
  expect_out_line "uid ($bob_uid, $bob_uid, $bob_uid)"
  expect_out_line "gid ($bob_gid, $bob_gid, $bob_gid)"
  end
}

begin exec-stay-setuid-actual-invoking-gid && {
  install -m 0440 /dev/stdin /etc/sudoers.d/exec-stay-setuid <<'EOF'
Defaults stay_setuid
ivan ALL = (ALL) NOPASSWD: ALL
EOF
  ivan_uid=$(id -u ivan); bob_uid=$(id -u bob)
  daemon_gid=$(getent group daemon | cut -d: -f3)
  run root "setpriv --reuid=ivan --regid=daemon --init-groups sudo -n -u bob /usr/bin/python3 -c 'import os; print(\"uid\", os.getresuid()); print(\"gid\", os.getresgid())'"
  expect_rc 0
  expect_out_line "uid ($ivan_uid, $bob_uid, $bob_uid)"
  expect_out_line "gid ($daemon_gid, $daemon_gid, $daemon_gid)"
  end
}

begin exec-nopty-command-foreground-handoff && {
  install -m 0440 /dev/stdin /etc/sudoers.d/exec-job-control <<'EOF'
Defaults !use_pty
EOF
  pty root "sudo -n /usr/bin/python3 -c 'import os; os.setpgid(0, 0); print(\"waiting-input\", flush=True); line=input(); print(\"foreground=\" + str(os.tcgetpgrp(0) == os.getpgrp()), flush=True); print(\"read=\" + line)'" \
    -e waiting-input -s 'continue\r' -e 'read=continue'
  expect_rc 0
  expect_out_has foreground=True
  end
}

begin exec-nopty-user-winch-relay && {
  install -m 0440 /dev/stdin /etc/sudoers.d/exec-signals <<'EOF'
Defaults !use_pty
EOF
  cat >/usr/local/bin/exec-winch.py <<'PY'
import os, signal, subprocess, sys, time
def received(signum, frame):
    print("winch-relayed", flush=True)
    sys.exit(0)
signal.signal(signal.SIGWINCH, received)
subprocess.Popen(["/bin/sh", "-c", "sleep 0.2; kill -WINCH %d" % os.getppid()],
                 start_new_session=True)
time.sleep(5)
sys.exit(2)
PY
  run root "sudo -n /usr/bin/python3 /usr/local/bin/exec-winch.py"
  expect_rc 0
  expect_out_line winch-relayed
  rm -f /usr/local/bin/exec-winch.py
  end
}

begin exec-nopty-shell-suspend-resume && {
  install -m 0440 /dev/stdin /etc/sudoers.d/exec-job-control <<'EOF'
Defaults !use_pty
EOF
  pty root 'PS1="OUTER> " /bin/bash --noprofile --norc -i' \
    -e 'OUTER> ' -s 'SHELL=/bin/bash sudo -s\r' \
    -s 'echo INNER-READY\r' -e '\r\nINNER-READY\r\n' \
    -s 'suspend\r' -e Stopped -s 'fg\r' \
    -s 'echo INNER-RESUMED; exit\r' -e '\r\nINNER-RESUMED\r\n' \
    -e 'OUTER> ' -s 'exit\r'
  expect_rc 0
  expect_out_has INNER-RESUMED
  end
}

begin exec-nopty-separate-group-stop-resume && {
  install -m 0440 /dev/stdin /etc/sudoers.d/exec-job-control <<'EOF'
Defaults !use_pty
EOF
  cat >/usr/local/bin/exec-stop-group.pl <<'PERL'
setpgrp(0, 0) or die "setpgrp: $!";
kill 'STOP', $$;
print "group-resumed\n";
PERL
  pty root 'PS1="OUTER> " /bin/bash --noprofile --norc -i' \
    -e 'OUTER> ' -s 'sudo /usr/bin/perl /usr/local/bin/exec-stop-group.pl\r' \
    -e Stopped -s 'fg\r' -e '\r\ngroup-resumed\r\n' \
    -e 'OUTER> ' -s 'exit\r'
  expect_rc 0
  expect_out_has group-resumed
  rm -f /usr/local/bin/exec-stop-group.pl
  end
}


exec_chroot_setup() {
  python3 - <<'PY'
import os, pathlib, shutil, subprocess
root = pathlib.Path("/srv/lean-sudo-jail")
shutil.rmtree(root, ignore_errors=True)
for directory in ("bin", "usr/bin", "etc", "work"):
    (root / directory).mkdir(parents=True, exist_ok=True)
for source, destination in (("/bin/dash", "/bin/sh"), ("/usr/bin/id", "/usr/bin/id")):
    shutil.copy2(source, str(root) + destination)
    for word in subprocess.check_output(["ldd", source], text=True).split():
        if word.startswith("/") and os.path.isfile(word):
            target = pathlib.Path(str(root) + word)
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(word, target)
(root / "usr/bin/jail-tool").write_text(
    '#!/bin/sh\nprintf "jail-marker\\ncwd=%s\\n" "$PWD"\n/usr/bin/id -u\n')
os.chmod(root / "usr/bin/jail-tool", 0o755)

(root / "etc/nsswitch.conf").write_text("passwd: unavailable\ngroup: unavailable\n")
PY
}



exec_chroot_files_only() {
  cp /etc/nsswitch.conf /tmp/exec-nsswitch.saved
  python3 - <<'PY'
from pathlib import Path
path = Path("/etc/nsswitch.conf")
text = path.read_text()
path.write_text("\n".join(line for line in text.splitlines()
                         if not line.lstrip().startswith("sudoers:"))
                + "\nsudoers: files\n")
PY
}

begin exec-chroot-rule-path-lookup && {
  exec_chroot_setup
  exec_chroot_files_only
  install -m 0440 /dev/stdin /etc/sudoers.d/exec-chroot <<'EOF'
root ALL = (ALL) CHROOT=/srv/lean-sudo-jail NOPASSWD: /usr/bin/jail-tool
EOF
  run root "sudo -n jail-tool"
  expect_rc 0
  expect_out_line jail-marker
  expect_out_line cwd=/
  expect_out_line 0
  expect_err_has '"CHROOT" is deprecated'
  mv /tmp/exec-nsswitch.saved /etc/nsswitch.conf
  rm -rf /srv/lean-sudo-jail
  end
}

begin exec-chroot-default && {
  exec_chroot_setup
  install -m 0440 /dev/stdin /etc/sudoers.d/exec-chroot <<'EOF'
Defaults runchroot=/srv/lean-sudo-jail
EOF
  run root "sudo -n jail-tool"
  expect_rc 0
  expect_out_line jail-marker
  expect_out_line cwd=/
  rm -rf /srv/lean-sudo-jail
  end
}

begin exec-chroot-user-root-wildcard && {
  exec_chroot_setup
  install -m 0440 /dev/stdin /etc/sudoers.d/exec-chroot <<'EOF'
root ALL = CHROOT=* NOPASSWD: /usr/bin/jail-tool
EOF
  run root "sudo -n -R /srv/lean-sudo-jail jail-tool"
  expect_rc 0
  expect_out_line jail-marker
  expect_err_has 'the -R option will be removed in a future version of sudo'
  rm -rf /srv/lean-sudo-jail
  end
}

begin exec-chroot-user-root-fixed-denied && {
  exec_chroot_setup
  install -m 0440 /dev/stdin /etc/sudoers.d/exec-chroot <<'EOF'
root ALL = CHROOT=/srv/lean-sudo-jail NOPASSWD: /usr/bin/jail-tool
EOF
  run root "sudo -n -R /srv/lean-sudo-jail jail-tool"
  expect_rc 1
  expect_err_has 'you are not permitted to use the -R option with /usr/bin/jail-tool'
  expect_out_empty
  rm -rf /srv/lean-sudo-jail
  end
}

begin exec-chroot-wildcard-without-user-root && {
  install -m 0440 /dev/stdin /etc/sudoers.d/exec-chroot <<'EOF'
root ALL = CHROOT=* NOPASSWD: ALL
EOF
  run root "sudo -n /bin/true"
  expect_rc 0
  end
}

begin exec-chroot-wildcard-literal-without-user-root && {
  install -m 0440 /dev/stdin /etc/sudoers.d/exec-chroot <<'EOF'
ivan ALL = CHROOT=* NOPASSWD: /bin/true
EOF
  run ivan "sudo -n /bin/true"
  expect_rc 0
  expect_out_empty
  end
}

begin exec-chroot-cwd-and-host-identity && {
  exec_chroot_setup
  exec_chroot_files_only
  install -m 0440 /dev/stdin /etc/sudoers.d/exec-chroot <<'EOF'
Defaults runchroot=/srv/lean-sudo-jail
root ALL = (bob) CWD=/work NOPASSWD: /usr/bin/jail-tool
EOF
  run root "sudo -n -u bob /usr/bin/jail-tool"
  expect_rc 0
  expect_out_line jail-marker
  expect_out_line cwd=/work
  expect_out_line "$(uid_of bob)"
  mv /tmp/exec-nsswitch.saved /etc/nsswitch.conf
  rm -rf /srv/lean-sudo-jail
  end
}

begin exec-chroot-last-rule-selects-namespace && {
  exec_chroot_setup
  exec_chroot_files_only
  cp -a /srv/lean-sudo-jail /srv/lean-sudo-jail-second
  printf '#!/bin/sh\nprintf "second-root\\n"\n' >/srv/lean-sudo-jail-second/usr/bin/jail-tool
  install -m 0440 /dev/stdin /etc/sudoers.d/exec-chroot <<'EOF'
root ALL = CHROOT=/srv/lean-sudo-jail NOPASSWD: /usr/bin/jail-tool, CHROOT=/srv/lean-sudo-jail-second /usr/bin/jail-tool
EOF
  run root "sudo -n jail-tool"
  expect_rc 0
  expect_out_line second-root
  mv /tmp/exec-nsswitch.saved /etc/nsswitch.conf
  rm -rf /srv/lean-sudo-jail /srv/lean-sudo-jail-second
  end
}

begin exec-chroot-fdexec-pins-jail-command && {
  exec_chroot_setup
  exec_chroot_files_only
  install -m 0440 /dev/stdin /etc/sudoers.d/exec-chroot <<'EOF'
Defaults fdexec=always
root ALL = CHROOT=/srv/lean-sudo-jail NOPASSWD: /bin/sh
EOF
  run root "sudo -n /bin/sh -c 'printf pinned-jail'"
  expect_rc 0
  expect_out_line pinned-jail
  mv /tmp/exec-nsswitch.saved /etc/nsswitch.conf
  rm -rf /srv/lean-sudo-jail
  end
}

begin exec-chroot-digest-uses-jail-bytes && {
  exec_chroot_setup
  exec_chroot_files_only
  digest=$(sha256sum /srv/lean-sudo-jail/bin/sh | cut -d' ' -f1)
  install -m 0440 /dev/stdin /etc/sudoers.d/exec-chroot <<EOF
root ALL = CHROOT=/srv/lean-sudo-jail NOPASSWD: sha256:$digest /bin/sh
EOF
  run root "sudo -n /bin/sh -c 'printf digested-jail'"
  expect_rc 0
  expect_out_line digested-jail
  mv /tmp/exec-nsswitch.saved /etc/nsswitch.conf
  rm -rf /srv/lean-sudo-jail
  end
}

begin exec-chroot-noexec-library-inside-jail && {
  exec_chroot_setup
  exec_chroot_files_only
  install -D -m 0755 /usr/libexec/sudo/sudo_noexec.so \
    /srv/lean-sudo-jail/usr/libexec/sudo/sudo_noexec.so
  install -m 0440 /dev/stdin /etc/sudoers.d/exec-chroot <<'EOF'
root ALL = CHROOT=/srv/lean-sudo-jail NOPASSWD: NOEXEC: /usr/bin/jail-tool
EOF
  run root "sudo -n jail-tool"
  expect_rc 126
  expect_out_line jail-marker
  expect_err_has 'Permission denied'
  mv /tmp/exec-nsswitch.saved /etc/nsswitch.conf
  rm -rf /srv/lean-sudo-jail
  end
}

begin exec-chroot-relative-symlink-contained && {
  exec_chroot_setup
  exec_chroot_files_only
  ln -s ../../bin/sh /srv/lean-sudo-jail/usr/bin/relative-shell
  install -m 0440 /dev/stdin /etc/sudoers.d/exec-chroot <<'EOF'
root ALL = CHROOT=/srv/lean-sudo-jail NOPASSWD: /usr/bin/relative-shell
EOF
  run root "sudo -n /usr/bin/relative-shell -c 'printf contained'"
  expect_rc 0
  expect_out_line contained
  mv /tmp/exec-nsswitch.saved /etc/nsswitch.conf
  rm -rf /srv/lean-sudo-jail
  end
}



begin exec-chroot-absolute-symlink-escape-refused && {
  exec_chroot_setup
  exec_chroot_files_only
  cp /srv/lean-sudo-jail/bin/sh /srv/lean-sudo-jail/bin/dash
  ln -s /bin/dash /srv/lean-sudo-jail/bin/outside
  install -m 0440 /dev/stdin /etc/sudoers.d/exec-chroot <<'EOF'
root ALL = CHROOT=/srv/lean-sudo-jail NOPASSWD: /bin/outside
EOF
  run root "sudo -n /bin/outside -c 'printf absolute-link'"
  if [[ $LABEL == reference ]]; then
    expect_rc 0
    expect_out_line absolute-link
  else
    expect_rc 1
    expect_out_empty
    expect_err_has '/bin/outside: command resolves outside the chroot directory'
  fi
  mv /tmp/exec-nsswitch.saved /etc/nsswitch.conf
  rm -rf /srv/lean-sudo-jail
  end
}



begin exec-chroot-empty-later-nss-retains-command && {
  exec_chroot_setup
  exec_chroot_files_only
  printf 'sudoers: files sss\n' >>/etc/nsswitch.conf
  python3 - <<'PY'
from pathlib import Path
p = Path("/etc/nsswitch.conf")
p.write_text(p.read_text().replace("sudoers: files\n", ""))
PY
  install -m 0440 /dev/stdin /etc/sudoers.d/exec-chroot <<'EOF'
root ALL = CHROOT=/srv/lean-sudo-jail NOPASSWD: /usr/bin/jail-tool
EOF
  run root "sudo -n jail-tool"
  if [[ $LABEL == reference ]]; then
    expect_rc 1
    expect_err_has 'jail-tool: command not found'
  else
    expect_rc 0
    expect_out_line jail-marker
  fi
  mv /tmp/exec-nsswitch.saved /etc/nsswitch.conf
  rm -rf /srv/lean-sudo-jail
  end
}



begin exec-chroot-nonroot-rule-lookup-retains-privileges && {
  exec_chroot_setup
  exec_chroot_files_only
  install -m 0440 /dev/stdin /etc/sudoers.d/exec-chroot <<'EOF'
root ALL = (bob) CHROOT=/srv/lean-sudo-jail CWD=/work NOPASSWD: /usr/bin/jail-tool
EOF
  run root "sudo -n -u bob /usr/bin/jail-tool"
  if [[ $LABEL == reference ]]; then
    expect_rc 1
    expect_err_has 'unable to set runas group vector: Operation not permitted'
  else
    expect_rc 0
    expect_out_line jail-marker
    expect_out_line cwd=/work
    expect_out_line "$(uid_of bob)"
  fi
  mv /tmp/exec-nsswitch.saved /etc/nsswitch.conf
  rm -rf /srv/lean-sudo-jail
  end
}

begin exec-chroot-glob-uses-jail-directory && {
  exec_chroot_setup
  exec_chroot_files_only
  install -m 0440 /dev/stdin /etc/sudoers.d/exec-chroot <<'EOF'
ivan ALL = CHROOT=/srv/lean-sudo-jail NOPASSWD: /usr/bin/jail-*
EOF
  run ivan "sudo -n jail-tool"
  expect_rc 0
  expect_out_line jail-marker
  mv /tmp/exec-nsswitch.saved /etc/nsswitch.conf
  rm -rf /srv/lean-sudo-jail
  end
}

begin exec-chroot-tilde-root-expands-on-host && {
  exec_chroot_setup
  exec_chroot_files_only
  ln -s /srv/lean-sudo-jail /root/exec-chroot-home
  install -m 0440 /dev/stdin /etc/sudoers.d/exec-chroot <<'EOF'
root ALL = CHROOT=~root/exec-chroot-home NOPASSWD: /usr/bin/jail-tool
EOF
  run root "sudo -n /usr/bin/jail-tool"
  if [[ $LABEL == reference ]]; then


    expect_rc 1
    expect_err_has '/usr/bin/jail-tool: command not found'
  else
    expect_rc 0
    expect_out_line jail-marker
  fi
  mv /tmp/exec-nsswitch.saved /etc/nsswitch.conf
  rm -rf /srv/lean-sudo-jail /root/exec-chroot-home
  end
}

begin exec-chroot-parent-symlink-escape-refused && {
  exec_chroot_setup
  exec_chroot_files_only
  cp /srv/lean-sudo-jail/bin/sh /srv/lean-sudo-jail/bin/dash
  ln -s /bin /srv/lean-sudo-jail/escape
  install -m 0440 /dev/stdin /etc/sudoers.d/exec-chroot <<'EOF'
root ALL = CHROOT=/srv/lean-sudo-jail NOPASSWD: /escape/dash
EOF
  run root "sudo -n /escape/dash -c 'printf parent-link'"
  if [[ $LABEL == reference ]]; then
    expect_rc 0
    expect_out_line parent-link
  else
    expect_rc 1
    expect_out_empty
    expect_err_has '/escape/dash: command resolves outside the chroot directory'
  fi
  mv /tmp/exec-nsswitch.saved /etc/nsswitch.conf
  rm -rf /srv/lean-sudo-jail
  end
}

begin exec-chroot-missing-noexec-fails-closed && {
  exec_chroot_setup
  exec_chroot_files_only
  install -m 0440 /dev/stdin /etc/sudoers.d/exec-chroot <<'EOF'
root ALL = CHROOT=/srv/lean-sudo-jail NOPASSWD: NOEXEC: /usr/bin/jail-tool
EOF
  run root "sudo -n jail-tool"
  if [[ $LABEL == reference ]]; then


    expect_rc 0
    expect_out_line jail-marker
  else
    expect_rc 1
    expect_out_empty
    expect_err_has 'unable to load noexec library'
  fi
  mv /tmp/exec-nsswitch.saved /etc/nsswitch.conf
  rm -rf /srv/lean-sudo-jail
  end
}

begin exec-chroot-tilde-root-host-command && {
  exec_chroot_setup
  exec_chroot_files_only
  ln -s /srv/lean-sudo-jail /root/exec-chroot-home
  install -m 0440 /dev/stdin /etc/sudoers.d/exec-chroot <<'EOF'
root ALL = CHROOT=~root/exec-chroot-home NOPASSWD: /bin/sh
EOF
  run root "sudo -n /bin/sh -c 'printf tilde-root'"
  expect_rc 0
  expect_out_line tilde-root
  mv /tmp/exec-nsswitch.saved /etc/nsswitch.conf
  rm -rf /srv/lean-sudo-jail /root/exec-chroot-home
  end
}



begin exec-chroot-wildcard-caller-tree-cannot-redirect-host && {
  exec_chroot_files_only
  install -m 0440 /dev/stdin /etc/sudoers.d/exec-chroot <<'EOF'
ivan ALL = (bob) CHROOT=* NOPASSWD: /usr/bin/ls
EOF
  run ivan "mkdir -p './*/tmp' './*/usr'; \
    ln -s ../tmp './*/usr/bin'; \
    printf '#!/bin/sh\necho wildcard-escape\n' > './*/tmp/ls'; \
    chmod 0755 './*/tmp/ls'; cp './*/tmp/ls' /tmp/ls; \
    printf 'ivanpw\n' | sudo -kS -u bob /tmp/ls"
  expect_rc 1
  expect_out_empty
  expect_err_has "not allowed to execute '/tmp/ls' as bob"
  rm -rf '/home/ivan/*' /tmp/ls
  mv /tmp/exec-nsswitch.saved /etc/nsswitch.conf
  end
}
