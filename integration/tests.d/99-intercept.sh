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
