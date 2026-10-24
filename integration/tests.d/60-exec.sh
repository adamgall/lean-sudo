# Execution hardening and sudo's child lifecycle.
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
  expect_out_line 42
  end
}

begin exec-pty-utmp-session && {
  install -m 0664 /dev/null /run/utmp
  install -m 0440 /dev/stdin /etc/sudoers.d/exec-utmp <<'EOF'
Defaults use_pty, set_utmp, utmp_runas
EOF
  # Ubuntu's uutils who uses systemd sessions, not the traditional utmp file.
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
  # sudo 1.9.17p2 exec_nopty.c calls terminate_command(pid, false):
  # only the command receives HUP/TERM/KILL, not its background descendants.
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
