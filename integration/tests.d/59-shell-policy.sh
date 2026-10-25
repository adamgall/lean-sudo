


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


shell_policy_syslog_fixture() {
  cat >"$WORK/shell-policy-syslog.py" <<'PY'
import re, subprocess, sys
sys.path.insert(0, '/usr/local/lib')
from sudo_it_logging import Syslog
binary, trace, kind = sys.argv[1:]
name = "shell_policy_missing_" + kind
options = ["-u", name] if kind == "user" else ["-u", "shell_policy_missing_user", "-g", name]
with Syslog() as logger:
    p = subprocess.run(["strace", "-f", "-s", "16384", "-e", "trace=sendto",
                        "-o", trace, "/bin/bash", "-c", 'exec -a sudo "$@"',
                        "sh", binary, "-n", *options, "/usr/bin/true"],
                       stdin=subprocess.DEVNULL, stdout=subprocess.PIPE,
                       stderr=subprocess.PIPE, timeout=20)
    sys.stderr.buffer.write(p.stderr)
    assert p.returncode == 1, (p.returncode, p.stdout, p.stderr)
    assert not p.stdout, p.stdout
    messages = []
    for message in logger.messages():

        match = re.search(r"sudo(?:\[\d+\])?: (.*)", message, re.S)
        if match and ("unknown user" in match[1] or "unknown group" in match[1]):
            messages.append(match[1])
    assert len(messages) == 1, messages
    assert "unknown " + kind + " " + name in messages[0], messages
    if kind == "group":
        assert "unknown user" not in messages[0], messages
    print(messages[0], end="")
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




for shell_policy_prompt in pam-default defaults-only cli-override cli-policy-disabled; do
  begin "shell-policy-prompt-$shell_policy_prompt" && {
    shell_policy_service=/etc/pam.d/shell-policy-oath
    shell_policy_secret=3132333435363738393031323334353637383930
    printf 'HOTP judy - %s\n' "$shell_policy_secret" >"$WORK/shell-policy.oath"
    chmod 0600 "$WORK/shell-policy.oath"
    shell_policy_code_reference=$(oathtool --hotp --counter=0 "$shell_policy_secret")
    shell_policy_code_actual=$(oathtool --hotp --counter=1 "$shell_policy_secret")
    cat >"$shell_policy_service" <<EOF
auth required pam_oath.so usersfile=$WORK/shell-policy.oath window=1 digits=6
@include common-account
@include common-session-noninteractive
EOF
    install -m 0440 /dev/stdin /etc/sudoers.d/zz-shell-policy <<EOF
Defaults:judy pam_service=${shell_policy_service##*/},lecture=never,passwd_tries=1
judy ALL=(root) /usr/bin/true
EOF
    shell_policy_options=
    shell_policy_expected_prompt="One-time password (OATH) for \`judy': "
    if [[ $shell_policy_prompt != pam-default ]]; then
      printf 'Defaults:judy passprompt="Configured %%u: "\n' >>/etc/sudoers.d/zz-shell-policy
    fi
    if [[ $shell_policy_prompt == cli-* ]]; then
      shell_policy_options="-p 'CLI %u: '"
      if [[ $shell_policy_prompt == cli-override ]]; then
        shell_policy_expected_prompt='CLI judy: '
      else


        printf 'Defaults:judy !passprompt_override\n' >>/etc/sudoers.d/zz-shell-policy
      fi
    fi
    shell_policy_compare judy "if [ \"\$SP_BINARY\" = /usr/bin/sudo.ws ]; then printf '%s\n' '$shell_policy_code_reference'; else printf '%s\n' '$shell_policy_code_actual'; fi | sp_sudo -kS $shell_policy_options /usr/bin/true" 0
    expect_out_empty
    printf '%s' "$shell_policy_expected_prompt" >"$WORK/shell-policy-prompt.err"
    cmp -s "$WORK/shell-policy-prompt.err" "$WORK/err" || fail 'PAM challenge selection/expansion differs from the expected prompt'

    shell_policy_compare judy "printf 'invalid-otp\\n' | sp_sudo -kS $shell_policy_options /usr/bin/true" 1
    expect_out_empty
    expect_err_has "$shell_policy_expected_prompt"
    expect_err_has '1 incorrect password attempt'
    rm -f "$shell_policy_service" "$WORK/shell-policy.oath" "$WORK/shell-policy.oath.lock"
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
