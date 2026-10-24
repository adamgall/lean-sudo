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
