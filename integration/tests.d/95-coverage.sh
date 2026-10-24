# Differential coverage against Ubuntu's installed sudo.ws 1.9.17p2.
# Each probe gets an independent cache; compare status and both output streams.
coverage_policy() {
  printf 'Defaults lecture=never, passwd_tries=1\n%s\n' "$1" > /etc/sudoers.d/zz-coverage
  chmod 0440 /etc/sudoers.d/zz-coverage
}
coverage_compare() {
  local user=$1 snippet=$2 expected=${3:-} ref_rc ref_out ref_err
  local root_hash
  root_hash=$(getent shadow root | cut -d: -f2)
  printf 'root:rootpw\n' | chpasswd
  rm -rf /run/sudo /run/lean-sudo
  run "$user" "S=/usr/bin/sudo.ws; $snippet"
  ref_rc=$RC ref_out=${OUT//sudo.ws/sudo} ref_err=${ERR//sudo.ws/sudo}
  [[ -z $expected || $RC == "$expected" ]] || fail "reference exit: expected $expected, got $RC"
  rm -rf /run/sudo /run/lean-sudo
  run "$user" "S=/usr/bin/sudo; $snippet"
  [[ $RC == "$ref_rc" ]] || fail "reference exit $ref_rc, actual $RC"
  [[ ${OUT//sudo.ws/sudo} == "$ref_out" ]] || fail "reference stdout: [$ref_out]; actual: [$OUT]"
  [[ ${ERR//sudo.ws/sudo} == "$ref_err" ]] || fail "reference stderr: [$ref_err]; actual: [$ERR]"
  usermod -p "$root_hash" root
}

coverage_errors=( '-z' '--preserve' '--not-an-option' '-u' '--user' '-l -v' '-U alice true' '-A -S true' '-i -s' '-i -E' '-C 2 true' '-T nonsense true' )
coverage_names=( invalid ambiguous unknown missing-short missing-long exclusive user-list askpass-stdin login-shell login-preserve closefrom timeout )
for coverage_i in "${!coverage_errors[@]}"; do
  begin "coverage-cli-${coverage_names[$coverage_i]}" && {
    coverage_compare bob "\$S ${coverage_errors[$coverage_i]}" 1
    end
  }
done

begin coverage-preserve-env-list && {
  coverage_policy 'bob ALL=(ALL:ALL) NOPASSWD: ALL'
  coverage_compare bob 'export FIRST=one SECOND=two THIRD=three; $S --preserve-env=FIRST,SECOND /bin/sh -c '\''printf "%s,%s,%s\n" "$FIRST" "$SECOND" "${THIRD-unset}"'\''' 0
  end
}
for coverage_pw in targetpw rootpw runaspw; do
  begin "coverage-auth-$coverage_pw-prompt-cache" && {
    coverage_policy "Defaults $coverage_pw, timestamp_type=global
alice ALL=(ALL:ALL) ALL"
    coverage_compare alice 'printf "rootpw\n" | $S -S -p "auth=%p: " /usr/bin/true; $S -n /usr/bin/true' 0
    end
  }
  begin "coverage-auth-$coverage_pw-list" && {
    coverage_policy "Defaults $coverage_pw
alice ALL=(ALL:ALL) ALL"
    coverage_compare alice 'printf "alicepw\n" | $S -S -p "auth=%p: " -l' 0
    end
  }
done
for coverage_option in listpw verifypw; do
  for coverage_value in all any always never; do
    begin "coverage-$coverage_option-$coverage_value" && {
      coverage_policy "Defaults $coverage_option=$coverage_value
bob ALL=(root) NOPASSWD: /usr/bin/true, PASSWD: /usr/bin/id"
      coverage_mode=-l; [[ $coverage_option == verifypw ]] && coverage_mode=-v
      coverage_compare bob "\$S -n $coverage_mode"
      end
    }
  done
done
for coverage_type in ppid global kernel; do
  begin "coverage-timestamp-$coverage_type" && {
    coverage_policy "Defaults timestamp_type=$coverage_type
alice ALL=(ALL) ALL"
    coverage_compare alice 'printf "alicepw\n" | $S -S -v; $S -n true; /bin/sh -c '\''"$1" -n true'\'' sh "$S"'
    end
  }
done
for coverage_timeout in 0 -1; do
  begin "coverage-timestamp-timeout-$coverage_timeout" && {
    coverage_policy "Defaults timestamp_type=global, timestamp_timeout=$coverage_timeout
alice ALL=(ALL) ALL"
    coverage_compare alice 'printf "alicepw\n" | $S -S -v; $S -n true'
    end
  }
done
for coverage_mask in 0022 0077 0777; do
  for coverage_override in umask_override '!umask_override'; do
    begin "coverage-umask-$coverage_mask-$coverage_override" && {
      coverage_policy "Defaults umask=$coverage_mask, $coverage_override"
      coverage_compare root 'umask 027; $S /bin/sh -c umask' 0
      end
    }
  done
done
for coverage_cwd in rule default option; do
  begin "coverage-login-cwd-$coverage_cwd" && {
    case $coverage_cwd in
      rule) coverage_policy 'root ALL=CWD=/tmp NOPASSWD: ALL'; coverage_args=;;
      default) coverage_policy 'Defaults runcwd=/tmp'; coverage_args=;;
      option) coverage_policy 'Defaults runcwd=*'; coverage_args='-D /tmp';;
    esac
    coverage_compare root "\$S -i $coverage_args /bin/pwd" 0
    end
  }
done
for coverage_shell in /bin/dash /bin/sh /usr/sbin/nologin; do
  begin "coverage-login-shell-${coverage_shell##*/}" && {
    coverage_old_shell=$(getent passwd bob | cut -d: -f7)
    usermod -s "$coverage_shell" bob
    coverage_compare root '$S -i -u bob /usr/bin/id -u'
    usermod -s "$coverage_old_shell" bob
    end
  }
done
begin coverage-shell-unset && {
  coverage_policy 'bob ALL=(ALL) NOPASSWD: ALL'
  coverage_compare bob 'unset SHELL; $S -s /usr/bin/printf "%s\n" shell-ok' 0
  end
}
for coverage_env in check wildcard coupling ps1 home-always home-set home-H pam; do
  begin "coverage-env-$coverage_env" && {
    coverage_policy 'bob ALL=(ALL:ALL) NOPASSWD: ALL'
    coverage_snippet=''
    case $coverage_env in
      check)
        printf 'Defaults env_check += "SAFE BADSLASH BADPERCENT TZ"\n' >>/etc/sudoers.d/zz-coverage
        coverage_snippet='export SAFE=good BADSLASH=a/b BADPERCENT=a%b TZ=UTC; $S /bin/sh -c '\''printf "%s|%s|%s|%s\n" "$SAFE" "${BADSLASH-unset}" "${BADPERCENT-unset}" "$TZ"'\''';;
      wildcard)
        printf 'Defaults env_keep += "*_PROXY X*Y"\n' >>/etc/sudoers.d/zz-coverage
        coverage_snippet='export HTTP_PROXY=proxy XmiddleY=match; $S /bin/sh -c '\''printf "%s|%s\n" "$HTTP_PROXY" "$XmiddleY"'\''';;
      coupling)
        printf 'Defaults env_keep += "LOGNAME"\n' >>/etc/sudoers.d/zz-coverage
        coverage_snippet='export LOGNAME=kept USER=other; $S /bin/sh -c '\''printf "%s|%s\n" "$LOGNAME" "$USER"'\''';;
      ps1) coverage_snippet='export SUDO_PS1=coverage-prompt; $S /usr/bin/printenv PS1';;
      home-always) printf 'Defaults always_set_home, env_keep += "HOME"\n' >>/etc/sudoers.d/zz-coverage; coverage_snippet='$S /usr/bin/printenv HOME';;
      home-set) printf 'Defaults set_home, env_keep += "HOME"\n' >>/etc/sudoers.d/zz-coverage; coverage_snippet='$S -s /usr/bin/printenv HOME';;
      home-H) printf 'Defaults env_keep += "HOME"\n' >>/etc/sudoers.d/zz-coverage; coverage_snippet='$S -H /usr/bin/printenv HOME';;
      pam)
        cp -a /etc/environment "$WORK/coverage-environment"
        printf 'COVERAGE_PAM=merged\nPYTHONPATH=/opt/coverage\n' >>/etc/environment
        coverage_snippet='$S /bin/sh -c '\''printf "%s|%s\n" "$COVERAGE_PAM" "$PYTHONPATH"'\''';;
    esac
    coverage_compare bob "$coverage_snippet" 0
    [[ $coverage_env != pam ]] || cp -a "$WORK/coverage-environment" /etc/environment
    end
  }
done
for coverage_mode in list validate; do
  begin "coverage-denied-$coverage_mode" && {
    coverage_policy 'Defaults !authenticate'
    coverage_args=-l; [[ $coverage_mode == validate ]] && coverage_args=-v
    coverage_compare bob "\$S $coverage_args" 1
    end
  }
done
begin coverage-list-unprivileged && {
  coverage_policy 'bob ALL=(root) NOPASSWD: /usr/bin/true'
  coverage_compare bob '$S -l' 0
  end
}
begin coverage-list-bound-defaults && {
  coverage_policy "User_Alias COVERAGE_USERS = bob
Host_Alias COVERAGE_HOSTS = $host
Defaults:COVERAGE_USERS umask=0077
Defaults@COVERAGE_HOSTS passwd_tries=2
bob ALL=(root) NOPASSWD: ALL"
  coverage_compare bob '$S -l' 0
  end
}
begin coverage-list-fqdn && {
  cp /etc/hosts "$WORK/coverage-hosts"
  printf '127.0.1.1 %s.coverage.test %s\n' "$host" "$host" > /etc/hosts
  coverage_policy 'Defaults fqdn
bob ALL=(root) NOPASSWD: ALL'
  coverage_compare bob '$S -l' 0
  cat "$WORK/coverage-hosts" > /etc/hosts
  end
}
begin coverage-list-remote-host && {
  coverage_policy 'bob coverage-remote=(root) NOPASSWD: ALL'
  coverage_compare root '$S -l -U bob -h coverage-remote' 0
  end
}
begin coverage-group-only-nonmember && {
  coverage_policy 'bob ALL=(:daemon) NOPASSWD: /usr/bin/id'
  coverage_compare bob '$S -g daemon /usr/bin/id' 0
  end
}
begin coverage-pty-fallback-no-tty && {
  coverage_policy 'Defaults use_pty'
  coverage_compare root '$S /usr/bin/python3 -c '\''import os; print(os.isatty(0), os.isatty(1), os.isatty(2))'\''' 0
  end
}

begin coverage-auth-timestamp-uid && {
  coverage_policy 'Defaults targetpw, timestamp_type=global
alice ALL=(ALL) ALL'
  coverage_compare alice 'printf "rootpw\n" | $S -S true; $S -n -u bob true' 1
  end
}
begin coverage-pwfeedback && {
  coverage_policy 'Defaults pwfeedback'
  pty alice 'sudo -k -p "coverage-password: " true' -e 'coverage-password:' -s 'alicepw\r'
  expect_rc 0
  expect_out_has '*******'
  end
}
begin coverage-passprompt-override-cli && {
  coverage_policy 'Defaults !passprompt_override, passprompt="default %p: "'
  coverage_compare alice 'printf "alicepw\n" | $S -kS -p "override %p: " true' 0
  expect_err_has 'override alice:'
  end
}

for coverage_edit in multiple user-group; do
  begin "coverage-sudoedit-$coverage_edit" && {
    coverage_policy 'bob ALL=(ALL:ALL) NOPASSWD: ALL'
    mkdir -p /var/lib/coverage-edit
    chmod 0755 /var/lib/coverage-edit
    printf '#!/bin/sh\nfor f do printf "edited\\n" >"$f"; done\n' >/usr/local/bin/coverage-editor
    chmod 0755 /usr/local/bin/coverage-editor
    coverage_args=''
    [[ $coverage_edit != user-group ]] || coverage_args='-u bob -g daemon'
    # Reset original bytes for each implementation, then compare persisted data.
    for coverage_impl in /usr/bin/sudo.ws /usr/bin/sudo; do
      printf 'original\n' >/var/lib/coverage-edit/one
      printf 'original\n' >/var/lib/coverage-edit/two
      chown bob:daemon /var/lib/coverage-edit/one /var/lib/coverage-edit/two
      run bob "SUDO_EDITOR=/usr/local/bin/coverage-editor $coverage_impl -e $coverage_args /var/lib/coverage-edit/one /var/lib/coverage-edit/two"
      expect_rc 0
      [[ $(cat /var/lib/coverage-edit/one) == edited ]] || fail 'first file not edited'
      [[ $(cat /var/lib/coverage-edit/two) == edited ]] || fail 'second file not edited'
      [[ $(stat -c '%U:%G' /var/lib/coverage-edit/one) == bob:daemon ]] || fail 'ownership changed'
    done
    rm -rf /var/lib/coverage-edit /usr/local/bin/coverage-editor
    end
  }
done

begin coverage-nopty-job-control && {
  coverage_policy 'Defaults !use_pty'
  pty root 'PS1="COVERAGE> " /bin/bash --norc -i' \
    -e 'COVERAGE> ' -s 'sudo /bin/cat\r' -s $'\032' \
    -e 'Stopped' -s 'fg\r' -s 'resumed\r' -e 'resumed' -s $'\004' \
    -e 'COVERAGE> ' -s 'exit\r'
  expect_rc 0
  expect_out_has Stopped
  end
}
for coverage_signal in WINCH HUP; do
  begin "coverage-signal-$coverage_signal" && {
    coverage_policy 'Defaults use_pty'
    # The child asks its independent helper to signal sudo, not itself.
    # The handler's output proves that sudo relayed the signal.
    cat >/usr/local/bin/coverage-signal.py <<'PY'
import os, signal, subprocess, sys, time
sig = getattr(signal, 'SIG' + sys.argv[1])
def received(signum, frame):
    print('relayed-' + sys.argv[1], flush=True)
    sys.exit(0)
signal.signal(sig, received)
# Find the front-end sudo above the pty monitor, without relying on PID text.
pid = os.getppid()
while True:
    with open('/proc/%d/stat' % pid) as f:
        fields = f.read().split()
    parent = int(fields[3])
    if parent <= 1:
        break
    with open('/proc/%d/comm' % parent) as f:
        if f.read().strip() not in ('sudo', 'sudo.ws'):
            break
    pid = parent
subprocess.Popen(['/bin/sh', '-c', 'sleep 0.2; kill -%s %d' % (sys.argv[1], pid)],
                 start_new_session=True)
print('signal-ready', flush=True)
time.sleep(5)
sys.exit(2)
PY
    pty root "sudo /usr/bin/python3 /usr/local/bin/coverage-signal.py $coverage_signal" -e "relayed-$coverage_signal"
    expect_rc 0
    expect_out_has "relayed-$coverage_signal"
    rm -f /usr/local/bin/coverage-signal.py
    end
  }
done

for coverage_tz in UTC :/etc/passwd ../etc/passwd 'bad%zone'; do
  coverage_tz_name=${coverage_tz//[^a-zA-Z0-9]/_}
  begin "coverage-env-check-TZ-$coverage_tz_name" && {
    coverage_policy 'bob ALL=(ALL) NOPASSWD: ALL'
    coverage_compare bob "export TZ='$coverage_tz'; \$S /bin/sh -c 'printf \"%s\\n\" \"\${TZ-unset}\"'" 0
    end
  }
done
