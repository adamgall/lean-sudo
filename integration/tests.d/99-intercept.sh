# Intercepted commands retain the original sudo caller and run-as identity.
for intercept_type in trace dso; do
  begin "intercept-${intercept_type}-subcommand-policy" && {
    install -m 0440 /dev/stdin /etc/sudoers.d/intercept <<EOF
Defaults intercept_type=$intercept_type, !use_pty
carol ALL=(root) NOPASSWD: INTERCEPT: /bin/sh, NOINTERCEPT: /usr/bin/id
EOF
    touch /tmp/intercept-protected
    run carol "sudo -n /bin/sh -c '/usr/bin/id -u; /bin/rm /tmp/intercept-protected; echo survived'"
    expect_rc 0
    expect_out_line 0
    expect_out_line survived
    expect_err_has 'not allowed to execute'
    [[ -f /tmp/intercept-protected ]] || fail 'denied subcommand deleted file'
    rm -f /tmp/intercept-protected
    end
  }

  begin "intercept-${intercept_type}-nested-shell" && {
    install -m 0440 /dev/stdin /etc/sudoers.d/intercept <<EOF
Defaults intercept_type=$intercept_type, !use_pty
carol ALL=(root) NOPASSWD: INTERCEPT: /bin/sh, NOINTERCEPT: /usr/bin/id
EOF
    run carol "sudo -n /bin/sh -c '/bin/sh -c \"/usr/bin/id -u; /usr/bin/true\"; echo nested-returned'"
    expect_rc 0
    expect_out_line 0
    expect_out_line nested-returned
    expect_err_has 'not allowed to execute'
    end
  }

  begin "intercept-${intercept_type}-log-subcmds" && {
    install -m 0440 /dev/stdin /etc/sudoers.d/intercept <<EOF
Defaults intercept_type=$intercept_type, log_subcmds, !use_pty, logfile="/tmp/intercept-log", !loglinelen
carol ALL=(root) NOPASSWD: /bin/sh
EOF
    rm -f /tmp/intercept-log
    run carol "sudo -n /bin/sh -c '/usr/bin/id -u; /usr/bin/true'"
    expect_rc 0
    expect_out_line 0
    grep -q 'COMMAND=/usr/bin/id -u' /tmp/intercept-log || fail 'missing id subcommand log'
    grep -q 'COMMAND=/usr/bin/true' /tmp/intercept-log || fail 'missing true subcommand log'
    rm -f /tmp/intercept-log
    end
  }

  begin "intercept-${intercept_type}-initial-setid-denied" && {
    install -m 4755 /usr/bin/id /tmp/intercept-setid
    install -m 0440 /dev/stdin /etc/sudoers.d/intercept <<EOF
Defaults intercept_type=$intercept_type, !intercept_allow_setid, !use_pty
carol ALL=(root) NOPASSWD: INTERCEPT: /tmp/intercept-setid
EOF
    run carol "sudo -n /tmp/intercept-setid -u"
    expect_rc 1
    expect_out_lacks '0'
    expect_err_has 'setid commands are not permitted in intercept mode'
    rm -f /tmp/intercept-setid
    end
  }

  begin "intercept-${intercept_type}-setid-denied" && {
    install -m 4755 /usr/bin/id /tmp/intercept-setid
    install -m 0440 /dev/stdin /etc/sudoers.d/intercept <<EOF
Defaults intercept_type=$intercept_type, !intercept_allow_setid, !use_pty
carol ALL=(root) NOPASSWD: INTERCEPT: /bin/sh, NOINTERCEPT: /tmp/intercept-setid
EOF
    run carol "sudo -n /bin/sh -c '/tmp/intercept-setid -u; echo setid-returned'"
    expect_rc 0
    expect_out_line setid-returned
    expect_out_lacks '0'
    expect_err_has 'not permitted'
    rm -f /tmp/intercept-setid
    end
  }

  begin "intercept-${intercept_type}-setid-allowed" && {
    install -m 4755 /usr/bin/id /tmp/intercept-setid
    install -m 0440 /dev/stdin /etc/sudoers.d/intercept <<EOF
Defaults intercept_type=$intercept_type, intercept_allow_setid, !use_pty
carol ALL=(root) NOPASSWD: INTERCEPT: /bin/sh, NOINTERCEPT: /tmp/intercept-setid
EOF
    run carol "sudo -n /bin/sh -c '/tmp/intercept-setid -u'"
    expect_rc 0
    expect_out_line 0
    rm -f /tmp/intercept-setid
    end
  }

  begin "intercept-${intercept_type}-authenticate-required" && {
    install -m 0440 /dev/stdin /etc/sudoers.d/intercept <<EOF
Defaults intercept_type=$intercept_type, intercept_authenticate, timestamp_timeout=0, !use_pty
carol ALL=(root) NOPASSWD: INTERCEPT: /bin/sh, PASSWD: NOINTERCEPT: /usr/bin/id
EOF
    run carol "sudo -n /bin/sh -c '/usr/bin/id -u; echo auth-returned'"
    expect_rc 0
    expect_out_line auth-returned
    expect_out_lacks '0'
    expect_err_has 'a password is required'
    end
  }

  begin "intercept-${intercept_type}-authenticate-disabled" && {
    install -m 0440 /dev/stdin /etc/sudoers.d/intercept <<EOF
Defaults intercept_type=$intercept_type, !intercept_authenticate, timestamp_timeout=0, !use_pty
carol ALL=(root) NOPASSWD: INTERCEPT: /bin/sh, PASSWD: NOINTERCEPT: /usr/bin/id
EOF
    run carol "sudo -n /bin/sh -c '/usr/bin/id -u'"
    expect_rc 0
    expect_out_line 0
    end
  }

  begin "intercept-${intercept_type}-pty-policy" && {
    install -m 0440 /dev/stdin /etc/sudoers.d/intercept <<EOF
Defaults intercept_type=$intercept_type, use_pty
carol ALL=(root) NOPASSWD: INTERCEPT: /bin/sh, NOINTERCEPT: /usr/bin/id
EOF
    pty carol "sudo -n /bin/sh -c '/usr/bin/id -u; /usr/bin/true; echo pty-returned'"
    expect_rc 0
    expect_out_has pty-returned
    expect_out_has 'not allowed to execute'
    end
  }

  begin "intercept-${intercept_type}-subcommand-environment" && {
    install -m 0440 /dev/stdin /etc/sudoers.d/intercept <<EOF
Defaults intercept_type=$intercept_type, !use_pty
carol ALL=(root) NOPASSWD: INTERCEPT: /bin/sh, NOINTERCEPT: /usr/bin/printenv
EOF
    run carol "sudo -n /bin/sh -c 'export INTERCEPT_TEST=changed; /usr/bin/printenv INTERCEPT_TEST'"
    expect_rc 0
    expect_out_line changed
    end
  }

  begin "intercept-${intercept_type}-syslog-subcommands" && {
    install -m 0440 /dev/stdin /etc/sudoers.d/intercept <<EOF
Defaults intercept_type=$intercept_type, log_subcmds, !use_pty
carol ALL=(root) NOPASSWD: /bin/sh
EOF
    cat >"$WORK/intercept-syslog.py" <<'PY'
import os, socket, subprocess, threading, tempfile
saved = None
sock = socket.socket(socket.AF_UNIX, socket.SOCK_DGRAM)
stop = threading.Event()
messages = []
try:
    if os.path.lexists("/dev/log"):
        fd, saved = tempfile.mkstemp(prefix="intercept-log-", dir="/dev")
        os.close(fd)
        os.replace("/dev/log", saved)
    sock.bind("/dev/log")
    sock.settimeout(.1)
    def receive():
        while True:
            try: messages.append(sock.recv(65536).decode(errors="replace"))
            except socket.timeout:
                if stop.is_set(): break
    thread = threading.Thread(target=receive)
    thread.start()
    result = subprocess.run(["runuser", "-u", "carol", "--", "sudo", "-n",
                             "/bin/sh", "-c", "/usr/bin/id -u; /usr/bin/true"],
                            capture_output=True, text=True)
    stop.set()
    thread.join()
    assert result.returncode == 0, result.stderr
    assert any("COMMAND=/usr/bin/id -u" in x for x in messages), messages
    assert any("COMMAND=/usr/bin/true" in x for x in messages), messages
    print("subcommands recorded in syslog")
finally:
    stop.set()
    sock.close()
    if os.path.lexists("/dev/log"): os.unlink("/dev/log")
    if saved is not None: os.replace(saved, "/dev/log")
PY
    run root "python3 '$WORK/intercept-syslog.py'"
    expect_rc 0
    expect_out_line 'subcommands recorded in syslog'
    rm -f "$WORK/intercept-syslog.py"
    end
  }

done

begin intercept-trace-empty-argv && {
  install -m 0440 /dev/stdin /etc/sudoers.d/intercept <<'EOF'
Defaults intercept_type=trace, !use_pty
carol ALL=(root) NOPASSWD: INTERCEPT: /usr/bin/python3, NOINTERCEPT: /usr/bin/id
EOF
  cat >/tmp/intercept-empty-argv.py <<'PY'
import ctypes
ctypes.CDLL(None).execve(b"/usr/bin/id", None, None)
raise SystemExit(99)
PY
  chmod 0644 /tmp/intercept-empty-argv.py
  run carol "sudo -n /usr/bin/python3 /tmp/intercept-empty-argv.py"
  expect_rc 0
  expect_out_has 'uid=0(root)'
  rm -f /tmp/intercept-empty-argv.py
  end
}

# Keep the command in sudo's foreground process group: an interactive shell
# with job control would put its children in another group and miss the broker.
# ptyrun already accepts literal terminal control bytes through -s.
for intercept_type in trace dso; do
  begin "intercept-${intercept_type}-nopty-terminal-signals" && {
    intercept_dir=$(mktemp -d /tmp/intercept-terminal.XXXXXX)
    chmod 0755 "$intercept_dir"
    install -o carol -m 0600 /dev/null "$intercept_dir/session"
    cat >"$intercept_dir/terminal.sh" <<'SH'
trap 'interrupted=yes; printf "\nINTERCEPT-INTERRUPTED\n"' INT
printf 'INTERCEPT-READY\n'
while :; do
    interrupted=no
    if IFS= read -r action; then
        case "$action" in
            id) /usr/bin/id -u; printf 'INTERCEPT-NEXT\n' ;;
            exit) exit 0 ;;
        esac
    elif [ "$interrupted" != yes ]; then
        exit 1
    fi
done
SH
    install -m 0440 /dev/stdin /etc/sudoers.d/intercept <<EOF
Defaults intercept_type=$intercept_type, !use_pty
carol ALL=(root) NOPASSWD: INTERCEPT: /bin/sh, NOINTERCEPT: /usr/bin/id
EOF
    pty carol "echo \$\$ > '$intercept_dir/session'; PS1='OUTER> ' exec /bin/bash --noprofile --norc -i" \
      -e 'OUTER> ' -s "sudo -n /bin/sh $intercept_dir/terminal.sh\r" \
      -e 'INTERCEPT-READY\r\n' -s $'\032' -e Stopped \
      -e 'OUTER> ' -s 'fg\r' -s 'id\r' -e '\r\n0\r\n' \
      -e 'INTERCEPT-NEXT\r\n' -s $'\003' -e 'INTERCEPT-INTERRUPTED\r\n' \
      -s 'id\r' -e '\r\n0\r\n' -e 'INTERCEPT-NEXT\r\n' \
      -s 'exit\r' -e 'OUTER> ' -s 'exit\r'
    expect_rc 0
    expect_out_lacks 'not allowed to execute'
    expect_out_lacks 'waitpid:'
    # Also clean up a stopped/stranded sudo, broker or command on failed steps.
    intercept_session=
    read -r intercept_session <"$intercept_dir/session" || :
    if [[ $intercept_session =~ ^[0-9]+$ && $intercept_session -gt 1 ]]; then
      pkill -KILL -s "$intercept_session" 2>/dev/null || :
    fi
    rm -rf "$intercept_dir"
    end
  }
done

begin intercept-trace-background-survives-command-exit && {
  intercept_dir=$(mktemp -d /tmp/intercept-background.XXXXXX)
  chmod 0755 "$intercept_dir"
  install -m 0440 /dev/stdin /etc/sudoers.d/intercept <<'EOF'
Defaults intercept_type=trace, !use_pty
carol ALL=(root) NOPASSWD: INTERCEPT: /bin/sh, NOINTERCEPT: /usr/bin/sleep
EOF
  cat >"$intercept_dir/background.sh" <<'SH'
/usr/bin/sleep 300 </dev/null >/dev/null 2>&1 &
child=$!
printf '%s\n' "$child" >"$1"
# Wait for the background exec, not for its completion. Otherwise the initial
# shell could exit before sleep's exec reaches the tracer at all.
attempt=0
while [ "$attempt" -lt 100 ]; do
    if IFS= read -r name <"/proc/$child/comm" && [ "$name" = sleep ]; then
        exit 0
    fi
    attempt=$((attempt + 1))
    /usr/bin/sleep .01
done
exit 1
SH
  run carol "sudo -n /bin/sh '$intercept_dir/background.sh' '$intercept_dir/pid'"
  expect_rc 0
  intercept_child=$(cat "$intercept_dir/pid" 2>/dev/null)
  if [[ $intercept_child =~ ^[0-9]+$ && $intercept_child -gt 1 ]]; then
    state=$(ps -o stat= -p "$intercept_child")
    [[ -n $state && $state != Z* ]] || fail 'trace teardown killed the background sleep'
    [[ $(cat "/proc/$intercept_child/comm" 2>/dev/null) == sleep ]] || \
      fail 'background descendant did not remain sleep'
    kill -KILL "$intercept_child" 2>/dev/null || :
  else
    fail 'background sleep did not publish its pid'
  fi
  rm -rf "$intercept_dir"
  end
}

for intercept_verify in intercept_verify '!intercept_verify'; do
  intercept_verify_name=verify
  [[ $intercept_verify == '!intercept_verify' ]] && intercept_verify_name=noverify
begin "intercept-trace-relative-script-$intercept_verify_name" && {
  intercept_dir=$(mktemp -d /tmp/intercept-relative.XXXXXX)
  chmod 0755 "$intercept_dir"
  cat >"$intercept_dir/safe.sh" <<'SH'
#!/bin/sh
printf 'script-label=%s\n' "$0"
/usr/bin/id -u
SH
  chmod 0755 "$intercept_dir/safe.sh"
  cat >"$intercept_dir/launch.py" <<'PY'
import os, sys
os.chdir(sys.argv[1])
os.execv("./safe.sh", [os.path.join(sys.argv[1], "safe.sh")])
PY
  install -m 0440 /dev/stdin /etc/sudoers.d/intercept <<EOF
Defaults intercept_type=trace, $intercept_verify, !use_pty
carol ALL=(root) NOPASSWD: INTERCEPT: /usr/bin/python3, NOINTERCEPT: $intercept_dir/safe.sh, /usr/bin/id
EOF
  run carol "sudo -n /usr/bin/python3 '$intercept_dir/launch.py' '$intercept_dir'"
  if [[ $intercept_verify == '!intercept_verify' ]]; then
    expect_rc 0
    expect_out_line "script-label=$intercept_dir/safe.sh"
    expect_out_line 0
  else
    # 1.9.17p2 rewrites the pathname but still verifies the original script
    # label, so relative script execution is killed before its first instruction.
    expect_rc 137
    expect_out_empty
    expect_err_has Killed
  fi
  rm -rf "$intercept_dir"
  end
}
done

# Reuse the exec fixtures' real jail and host-only NSS lookup. Separate verify
# modes keep authorization failures distinguishable from inode verification.
for intercept_verify in intercept_verify '!intercept_verify'; do
  intercept_verify_name=verify
  [[ $intercept_verify == '!intercept_verify' ]] && intercept_verify_name=noverify
  begin "intercept-trace-chroot-subcommands-$intercept_verify_name" && {
    exec_chroot_setup
    exec_chroot_files_only
    python3 - <<'PY'
import os, pathlib, shutil, subprocess
root = pathlib.Path("/srv/lean-sudo-jail")
shutil.copy2("/usr/bin/rm", root / "usr/bin/rm")
for word in subprocess.check_output(["ldd", "/usr/bin/rm"], text=True).split():
    if word.startswith("/") and os.path.isfile(word):
        target = pathlib.Path(str(root) + word)
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(word, target)
(root / "work/intercept-protected").touch()
PY
    install -m 0440 /dev/stdin /etc/sudoers.d/intercept <<EOF
Defaults intercept_type=trace, $intercept_verify, !use_pty
carol ALL=(root) CHROOT=/srv/lean-sudo-jail NOPASSWD: INTERCEPT: /bin/sh, NOINTERCEPT: /usr/bin/id
EOF
    run carol "sudo -n /bin/sh -c '/usr/bin/id -u; /usr/bin/rm /work/intercept-protected; echo jail-returned'"
    expect_rc 0
    if [[ $intercept_verify == '!intercept_verify' ]]; then
      expect_out_line 0
    else
      expect_err_has 'Killed'
      [[ $OUT == jail-returned ]] || fail 'verified jail subcommand unexpectedly ran'
    fi
    expect_out_line jail-returned
    expect_err_has 'not allowed to execute'
    [[ -f /srv/lean-sudo-jail/work/intercept-protected ]] || fail 'denied jail subcommand deleted file'
    mv /tmp/exec-nsswitch.saved /etc/nsswitch.conf
    rm -rf /srv/lean-sudo-jail
    end
  }
done

# A custom script interpreter pauses before opening the script, so CLONE_FS
# changes its cwd after authorization without relying on a scheduler race.
# ctypes supplies clone without adding a compiler dependency to the test image.
# The nested Python shebang needs !intercept_verify; the ordinary shell-script
# fixture above separately checks the absolute label with verification enabled.
begin intercept-trace-relative-script-clone-fs && {
  intercept_dir=$(mktemp -d /tmp/intercept-clone-fs.XXXXXX)
  chmod 0755 "$intercept_dir"
  mkdir "$intercept_dir/approved" "$intercept_dir/decoy"
  cat >"$intercept_dir/interpreter" <<'PY'
#!/usr/bin/python3
import os, sys
label, ready, proceed = sys.argv[1:]
ready, proceed = int(ready), int(proceed)
os.write(ready, b"R")
os.close(ready)
if os.read(proceed, 1) != b"G":
    raise SystemExit("missing cwd-switch handshake")
os.close(proceed)
print("script-label=" + label)
print("shared-cwd=" + os.getcwd())
with open(label) as script:
    script.readline()  # shebang
    sys.stdout.write(script.read())
PY
  chmod 0755 "$intercept_dir/interpreter"
  printf '#!%s/interpreter\napproved-script\n' "$intercept_dir" >"$intercept_dir/approved/safe.script"
  printf '#!%s/interpreter\nunapproved-script\n' "$intercept_dir" >"$intercept_dir/decoy/safe.script"
  chmod 0755 "$intercept_dir/approved/safe.script" "$intercept_dir/decoy/safe.script"
  cat >"$intercept_dir/launch.py" <<'PY'
import ctypes, os, signal, sys

libc = ctypes.CDLL(None, use_errno=True)
entry_type = ctypes.CFUNCTYPE(ctypes.c_int, ctypes.c_void_p)
libc.clone.argtypes = (entry_type, ctypes.c_void_p, ctypes.c_int, ctypes.c_void_p)
libc.clone.restype = ctypes.c_int
libc.prctl.argtypes = (ctypes.c_int, ctypes.c_ulong, ctypes.c_ulong,
                      ctypes.c_ulong, ctypes.c_ulong)
libc.prctl.restype = ctypes.c_int
ready = os.pipe()
proceed = os.pipe()
os.set_inheritable(ready[1], True)
os.set_inheritable(proceed[0], True)
parent = os.getpid()
os.chdir(sys.argv[1])

@entry_type
def child_main(_):
    try:
        # Failed/timeout runs must not leave the interpreter behind.
        if libc.prctl(1, signal.SIGKILL, 0, 0, 0) != 0 or os.getppid() != parent:
            os._exit(97)
        os.close(ready[0])
        os.close(proceed[1])
        os.execv("./safe.script", ["./safe.script", str(ready[1]), str(proceed[0])])
    except BaseException:
        os._exit(98)

stack = ctypes.create_string_buffer(1024 * 1024)
stack_top = (ctypes.addressof(stack) + len(stack)) & ~15
child = -1
try:
    child = libc.clone(child_main, stack_top, 0x200 | signal.SIGCHLD, None)  # CLONE_FS
    if child < 0:
        raise OSError(ctypes.get_errno(), "clone(CLONE_FS)")
    os.close(ready[1])
    os.close(proceed[0])
    if os.read(ready[0], 1) != b"R":
        raise RuntimeError("script interpreter did not reach the handshake")
    os.chdir(sys.argv[2])
    os.write(proceed[1], b"G")
    _, status = os.waitpid(child, 0)
    child = -1
    raise SystemExit(os.waitstatus_to_exitcode(status))
finally:
    if child > 0:
        try:
            os.kill(child, signal.SIGKILL)
        except ProcessLookupError:
            pass
        os.waitpid(child, 0)
    for fd in (*ready, *proceed):
        try:
            os.close(fd)
        except OSError:
            pass
PY
  install -m 0440 /dev/stdin /etc/sudoers.d/intercept <<EOF
Defaults intercept_type=trace, !intercept_verify, !use_pty
carol ALL=(root) NOPASSWD: INTERCEPT: /usr/bin/python3, NOINTERCEPT: $intercept_dir/approved/safe.script
EOF
  run carol "sudo -n /usr/bin/python3 '$intercept_dir/launch.py' '$intercept_dir/approved' '$intercept_dir/decoy'"
  expect_rc 0
  expect_out_line "script-label=$intercept_dir/approved/safe.script"
  expect_out_line "shared-cwd=$intercept_dir/decoy"
  expect_out_line approved-script
  expect_out_lacks unapproved-script
  rm -rf "$intercept_dir"
  end
}
