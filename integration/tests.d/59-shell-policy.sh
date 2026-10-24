# Second shell audit, rows 14/16/19/20 of ResidualGaps2. Expectations are
# pinned both semantically and byte-for-byte against Ubuntu's installed sudo.ws.
# Use the same argv[0], rather than rewriting arbitrary diagnostic text.
shell_policy_compare() {
  local user=$1 snippet=$2 expected=$3 audit=${4:-} binary side
  for side in reference actual; do
    binary=/usr/bin/sudo.ws
    [[ $side == actual ]] && binary=/usr/bin/sudo
    run "$user" "SP_BINARY=$binary; sp_sudo() { /bin/bash -c 'exec -a sudo \"\$@\"' sh \"\$SP_BINARY\" \"\$@\"; }; $snippet"
    expect_rc "$expected"
    cp "$WORK/out" "$WORK/shell-policy-$side.out"
    cp "$WORK/err" "$WORK/shell-policy-$side.err"
    if [[ $audit == audit ]]; then
      shell_policy_check_no_audit || fail "$side: unexpected USER_CMD audit record during identity initialization"
    fi
  done
  diff -u "$WORK/shell-policy-reference.out" "$WORK/shell-policy-actual.out" >>"$LOG" || fail 'stdout differs from sudo.ws'
  diff -u "$WORK/shell-policy-reference.err" "$WORK/shell-policy-actual.err" >>"$LOG" || fail 'stderr differs from sudo.ws'
}

# The reference has not populated runas.argv at this initialization failure, so
# audit_failure emits no USER_CMD record. Reuse 57's decoder for both dispositions,
# preserving its trace file because filtered runs still source that helper.
shell_policy_check_no_audit() (
  local saved=
  [[ -s $WORK/shell-policy.audit ]] || return 1
  if [[ -e /tmp/shell-residual.audit ]]; then
    saved=$(mktemp "$WORK/shell-policy-audit-save.XXXXXX")
    cp -a /tmp/shell-residual.audit "$saved"
  fi
  trap 'if [[ -n $saved ]]; then cp -a "$saved" /tmp/shell-residual.audit; rm -f "$saved"; else rm -f /tmp/shell-residual.audit; fi' EXIT
  cp "$WORK/shell-policy.audit" /tmp/shell-residual.audit
  ! { shell_residual_audit_record failed >/dev/null ||
      shell_residual_audit_record success >/dev/null; }
)

for shell_policy_unknown in user group group-before-user user-after-group; do
  begin "shell-policy-unknown-$shell_policy_unknown" && {
    case $shell_policy_unknown in
      user) shell_policy_options='-u shell_policy_missing_user'; shell_policy_reason='unknown user shell_policy_missing_user' ;;
      group) shell_policy_options='-g shell_policy_missing_group'; shell_policy_reason='unknown group shell_policy_missing_group' ;;
      group-before-user) shell_policy_options='-u shell_policy_missing_user -g shell_policy_missing_group'; shell_policy_reason='unknown group shell_policy_missing_group' ;;
      user-after-group) shell_policy_options='-g shell_policy_missing_group -u shell_policy_missing_user'; shell_policy_reason='unknown group shell_policy_missing_group' ;;
    esac
    shell_policy_compare judy "sp_sudo -n $shell_policy_options /usr/bin/true" 1
    expect_out_empty
    printf 'sudo: %s\nsudo: error initializing audit plugin sudoers_audit\n' "$shell_policy_reason" >"$WORK/shell-policy-expected.err"
    cmp -s "$WORK/shell-policy-expected.err" "$WORK/err" || fail 'unknown identity must emit exactly the lookup error then the audit-plugin initialization error'
    end
  }
done

# Capture actual syslog datagrams, not a logfile surrogate. A pre-existing
# /dev/log is moved aside and restored in finally, including on probe failure.
shell_policy_syslog_fixture() {
  cat >"$WORK/shell-policy-syslog.py" <<'PY'
import os, re, socket, subprocess, sys, tempfile
binary, trace, kind = sys.argv[1:]
name = "shell_policy_missing_" + kind
options = ["-u", name] if kind == "user" else ["-u", "shell_policy_missing_user", "-g", name]
saved = None
sock = socket.socket(socket.AF_UNIX, socket.SOCK_DGRAM)
try:
    if os.path.lexists("/dev/log"):
        fd, saved = tempfile.mkstemp(prefix="shell-policy-log-", dir="/dev")
        os.close(fd)
        os.replace("/dev/log", saved)
    sock.bind("/dev/log")
    sock.settimeout(0.1)
    p = subprocess.run(["strace", "-f", "-s", "16384", "-e", "trace=sendto",
                        "-o", trace, "/bin/bash", "-c", 'exec -a sudo "$@"',
                        "sh", binary, "-n", *options, "/usr/bin/true"],
                       stdin=subprocess.DEVNULL, stdout=subprocess.PIPE,
                       stderr=subprocess.PIPE, timeout=20)
    sys.stderr.buffer.write(p.stderr)
    assert p.returncode == 1, (p.returncode, p.stdout, p.stderr)
    assert not p.stdout, p.stdout
    messages = []
    while True:
        try:
            message = sock.recv(65536).decode()
        except socket.timeout:
            break
        # Only transport timestamp, process ID, and program prefix vary.
        match = re.search(r"sudo(?:\[\d+\])?: (.*)", message, re.S)
        if match and ("unknown user" in match[1] or "unknown group" in match[1]):
            messages.append(match[1])
    assert len(messages) == 1, messages
    assert "unknown " + kind + " " + name in messages[0], messages
    if kind == "group":
        assert "unknown user" not in messages[0], messages
    print(messages[0], end="")
finally:
    sock.close()
    if os.path.lexists("/dev/log") and (saved is not None or os.path.exists("/dev/log")):
        os.unlink("/dev/log")
    if saved is not None:
        os.replace(saved, "/dev/log")
PY
}

for shell_policy_kind in user group; do
  begin "shell-policy-unknown-$shell_policy_kind-events" && {
    shell_policy_syslog_fixture
    shell_policy_compare root "python3 '$WORK/shell-policy-syslog.py' \"\$SP_BINARY\" '$WORK/shell-policy.audit' '$shell_policy_kind'" 0 audit
    expect_out_has "unknown $shell_policy_kind shell_policy_missing_$shell_policy_kind"
    expect_err_has 'error initializing audit plugin sudoers_audit'
    rm -f "$WORK/shell-policy-syslog.py" "$WORK/shell-policy.audit"
    end
  }
done

# A sudoedit-only grant must not authorize either shell mode. Conversely, a
# shell-only grant must permit the shell to invoke sudoedit as an ordinary word.
# The nested sudoedit runs as root and uses /usr/bin/true as its editor.
for shell_policy_mode in shell login; do
  shell_policy_flag=-s
  [[ $shell_policy_mode == login ]] && shell_policy_flag=-i
  for shell_policy_grant in edit-only shell-only; do
    begin "shell-policy-$shell_policy_mode-sudoedit-$shell_policy_grant" && {
      shell_policy_file=$(mktemp /etc/shell-policy-edit.XXXXXX)
      printf 'shell policy sentinel\n' >"$shell_policy_file"
      install -m 0440 /dev/stdin /etc/sudoers.d/zz-shell-policy <<EOF
Defaults:judy !authenticate,lecture=never,env_keep+="SUDO_EDITOR"
Defaults:root lecture=never,editor=/usr/bin/true
EOF
      if [[ $shell_policy_grant == edit-only ]]; then
        printf 'judy ALL=(root) NOPASSWD: sudoedit %s\n' "$shell_policy_file" >>/etc/sudoers.d/zz-shell-policy
        shell_policy_expected=1
      else
        printf 'judy ALL=(root) NOPASSWD: /bin/bash\n' >>/etc/sudoers.d/zz-shell-policy
        shell_policy_expected=0
      fi
      XENV=(SUDO_EDITOR=/usr/bin/true)
      shell_policy_compare judy "sp_sudo -n $shell_policy_flag sudoedit '$shell_policy_file'" "$shell_policy_expected"
      expect_out_empty
      expect_err_lacks "sudoedit doesn't need to be run via sudo"
      if [[ $shell_policy_grant == edit-only ]]; then
        expect_err_has 'not allowed to execute'
        expect_err_lacks 'unchanged'
      else
        expect_err_has "$shell_policy_file unchanged"
      fi
      [[ $(cat "$shell_policy_file") == 'shell policy sentinel' ]] || fail 'sudoedit fixture changed'
      rm -f "$shell_policy_file"
      end
    }
  done
done

# pam_ftp is already supplied by the image's libpam-modules. For a non-FTP
# user it asks a non-generic challenge, sets PAM_AUTHTOK, and returns failure;
# sufficient ignores that failure, then pam_unix validates the real password.
# No custom module/compiler and no replacement of /etc/pam.d/sudo are needed.
# Source: linux-pam v1.7.0 modules/pam_ftp/pam_ftp.c (PLEASE_ENTER_PASSWORD).
for shell_policy_prompt in pam-default defaults-only cli-override cli-policy-disabled; do
  begin "shell-policy-prompt-$shell_policy_prompt" && {
    # libpam lowercases service names; shell mktemp's mixed-case suffix would
    # silently select /etc/pam.d/other instead. Python's tempfile alphabet is
    # lowercase, with an assertion guarding the actual fixture name.
    shell_policy_service=$(python3 - <<'PY'
import os, tempfile
fd, path = tempfile.mkstemp(prefix="shell-policy.", dir="/etc/pam.d")
os.close(fd)
if path != path.lower():
    os.unlink(path)
    raise RuntimeError("PAM fixture service name must be lowercase")
print(path)
PY
    )
    chmod 0644 "$shell_policy_service"
    cat >"$shell_policy_service" <<'EOF'
auth sufficient pam_ftp.so
auth required pam_unix.so use_first_pass
account required pam_permit.so
session required pam_permit.so
EOF
    install -m 0440 /dev/stdin /etc/sudoers.d/zz-shell-policy <<EOF
Defaults:judy pam_service=${shell_policy_service##*/},lecture=never,passwd_tries=1
judy ALL=(root) /usr/bin/true
EOF
    shell_policy_options=
    shell_policy_expected_prompt='Password required for judy.'
    if [[ $shell_policy_prompt != pam-default ]]; then
      printf 'Defaults:judy passprompt="Configured %%u: "\n' >>/etc/sudoers.d/zz-shell-policy
    fi
    if [[ $shell_policy_prompt == cli-* ]]; then
      shell_policy_options="-p 'CLI %u: '"
      if [[ $shell_policy_prompt == cli-override ]]; then
        shell_policy_expected_prompt='CLI judy: '
      else
        # -p seeds the default before sudoers is evaluated; explicit policy can
        # turn that override back off without changing the PAM challenge.
        printf 'Defaults:judy !passprompt_override\n' >>/etc/sudoers.d/zz-shell-policy
      fi
    fi
    shell_policy_compare judy "printf 'judypw\\n' | sp_sudo -kS $shell_policy_options /usr/bin/true" 0
    expect_out_empty
    printf '%s' "$shell_policy_expected_prompt" >"$WORK/shell-policy-prompt.err"
    cmp -s "$WORK/shell-policy-prompt.err" "$WORK/err" || fail 'PAM challenge selection/expansion differs from the expected prompt'
    # Prove this is authentication, not a permissive fixture accepting anything.
    shell_policy_compare judy "printf 'incorrect-shell-policy-password\\n' | sp_sudo -kS $shell_policy_options /usr/bin/true" 1
    expect_out_empty
    expect_err_has "$shell_policy_expected_prompt"
    expect_err_has '1 incorrect password attempt'
    rm -f "$shell_policy_service"
    end
  }
done

for shell_policy_relative in environment logfile list; do
  begin "shell-policy-relative-$shell_policy_relative" && {
    shell_policy_dir=$(mktemp -d /home/judy/shell-policy.XXXXXX)
    chmod 0755 "$shell_policy_dir"
    cat >"$shell_policy_dir/foo" <<'EOF'
#!/bin/sh
/usr/bin/printenv SUDO_COMMAND
EOF
    chmod 0755 "$shell_policy_dir/foo"
    install -m 0440 /dev/stdin /etc/sudoers.d/zz-shell-policy <<EOF
Defaults:judy lecture=never,logfile=$WORK/shell-policy-command.log,loglinelen=0
judy ALL=(root) NOPASSWD: $shell_policy_dir/foo
EOF
    if [[ $shell_policy_relative == list ]]; then
      shell_policy_compare judy "cd '$shell_policy_dir' && sp_sudo -n -l ./foo 'argument with space'" 0
    else
      shell_policy_compare judy "cd '$shell_policy_dir' && sp_sudo -n ./foo 'argument with space'" 0
    fi
    printf './foo argument with space\n' >"$WORK/shell-policy-relative.out"
    cmp -s "$WORK/shell-policy-relative.out" "$WORK/out" || fail 'relative command spelling/arguments were not preserved'
    [[ ! -s $WORK/err ]] || fail 'unexpected relative-command stderr'
    if [[ $shell_policy_relative == logfile ]]; then
      # The reference preserves relative spelling in SUDO_COMMAND and -l, but
      # logs the absolute pathname and shell-quotes the argument containing
      # spaces. Require exactly one reference event and one matching event.
      python3 - "$WORK/shell-policy-command.log" "$shell_policy_dir/foo" <<'PY' >>"$LOG" 2>&1 || fail 'logfile command fields differ from the reference absolute path and quoted arguments'
import sys
lines = open(sys.argv[1]).read().splitlines()
commands = [line.split(" ; COMMAND=", 1)[1] for line in lines if " ; COMMAND=" in line]
expected = sys.argv[2] + " 'argument with space'"
assert commands == [expected, expected], lines
PY
    fi
    rm -f "$shell_policy_dir/foo" "$WORK/shell-policy-command.log"
    rmdir "$shell_policy_dir"
    end
  }
done
