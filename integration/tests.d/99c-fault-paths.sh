cat >"$WORK/fault-seccomp.py" <<'PY'
import ctypes
import errno
import os
import platform
import struct
import sys

ARCHES = {
    'aarch64': (0xC00000B7, {'close_range': 436, 'prlimit64': 261, 'setrlimit': 164}),
    'x86_64': (0xC000003E, {'close_range': 436, 'prlimit64': 302, 'setrlimit': 160}),
}
LIMITS = {'cpu': 0, 'fsize': 1, 'data': 2, 'stack': 3, 'core': 4, 'rss': 5, 'nproc': 6,
          'nofile': 7, 'memlock': 8, 'as': 9, 'locks': 10}
LOAD, JEQ, RET = 0x20, 0x15, 0x06
ALLOW, ERRNO = 0x7FFF0000, 0x00050000


def block(nr, checks, error):
    code = [('ld', 0), ('jeq', nr, 'next', 'fail')]
    for kind, index, value in checks:
        if kind == 'eq':
            code += [('ld', 16 + 8 * index), ('jeq', value, 'next', 'fail')]
        else:
            code += [('ld', 16 + 8 * index), ('jeq', 0, 'next', 'match'),
                     ('ld', 20 + 8 * index), ('jeq', 0, 'fail', 'match')]
    code.append(('ret', ERRNO | error))
    match, fail = len(code) - 1, len(code)
    resolved = []
    for position, item in enumerate(code):
        if item[0] != 'jeq':
            resolved.append(item)
            continue
        jumps = [{'next': position + 1, 'match': match, 'fail': fail}[label] - position - 1
                 for label in item[2:]]
        resolved.append(('jeq', item[1], jumps[0], jumps[1]))
    return resolved


def program(arch, numbers, close_range, limits):
    blocks = []
    if close_range:
        blocks += block(numbers['close_range'], [], errno.ENOSYS)
    for name in limits:
        resource = LIMITS[name]
        blocks += block(numbers['prlimit64'], [('eq', 1, resource), ('nonnull', 2, 0)],
                        errno.EPERM)
        blocks += block(numbers['setrlimit'], [('eq', 0, resource), ('nonnull', 1, 0)],
                        errno.EPERM)
    code = [('ld', 4), ('jeq', arch, 0, len(blocks))] + blocks + [('ret', ALLOW)]
    raw = b''
    for item in code:
        if item[0] == 'ld':
            raw += struct.pack('=HBBI', LOAD, 0, 0, item[1])
        elif item[0] == 'jeq':
            raw += struct.pack('=HBBI', JEQ, item[2], item[3], item[1])
        else:
            raw += struct.pack('=HBBI', RET, 0, 0, item[1])
    return raw


class Fprog(ctypes.Structure):
    _fields_ = [('len', ctypes.c_ushort), ('filter', ctypes.c_void_p)]


def main():
    args = sys.argv[1:]
    split = args.index('--')
    options, command = args[:split], args[split + 1:]
    close_range = '--close-range' in options
    limits = [option.split('=', 1)[1] for option in options if option.startswith('--rlimit=')]
    arch, numbers = ARCHES[platform.machine()]
    raw = program(arch, numbers, close_range, limits)
    libc = ctypes.CDLL(None, use_errno=True)
    buffer = ctypes.create_string_buffer(raw, len(raw))
    prog = Fprog(len(raw) // 8, ctypes.cast(buffer, ctypes.c_void_p))
    if libc.prctl(22, 2, ctypes.byref(prog), 0, 0) != 0:
        raise SystemExit('seccomp: ' + os.strerror(ctypes.get_errno()))
    libc.syscall.restype = ctypes.c_long
    if close_range:
        result = libc.syscall(ctypes.c_long(numbers['close_range']), ctypes.c_uint(1000000),
                              ctypes.c_uint(1000000), ctypes.c_uint(0))
        if result != -1 or ctypes.get_errno() != errno.ENOSYS:
            raise SystemExit('close_range filter is not effective')
    for name in limits:
        current = (ctypes.c_ulonglong * 2)()
        if libc.prlimit(0, LIMITS[name], None, current) != 0:
            raise SystemExit('getrlimit is blocked for ' + name)
        if libc.prlimit(0, LIMITS[name], current, None) == 0 or ctypes.get_errno() != errno.EPERM:
            raise SystemExit('setrlimit filter is not effective for ' + name)
    os.execvp(command[0], command)


main()
PY

cat >"$WORK/fault-audit.py" <<'PY'
import json
import re
import sys

volatile = {'uuid', 'timestamp', 'run_time'}
process = {'pid', 'ppid', 'pgid', 'tcpgid', 'sid'}
try:
    text = open(sys.argv[1]).read()
except FileNotFoundError:
    print('no audit log')
    sys.exit(0)
text = re.sub(r'(?m)^(\s+)"(?:submit_argv|submit_envp|run_argv|run_envp)": (?=")', r'\1', text)
records = []
for kind, record in json.loads(text, object_pairs_hook=list):
    record = {key: value for key, value in record if key not in volatile}
    if 'user_info' in record:
        record['user_info'] = sorted([key, value] for key, value in record['user_info']
                                     if key not in process)
    for key in ('command_info', 'options'):
        if key in record:
            record[key] = sorted([name, value] for name, value in record[key])
    for key in ('submit_envp', 'run_envp'):
        if key in record:
            record[key] = sorted(record[key])
    if 'submit_argv' in record:
        record['submit_argv'] = ['sudo'] + record['submit_argv'][1:]
    records.append([kind, record])
print(json.dumps(records, indent=1, sort_keys=True))
PY

cat >"$WORK/fault-zone.py" <<'PY'
import datetime
import os
import subprocess
import sys
import tempfile

directory = sys.argv[1]
now = datetime.datetime.now(datetime.timezone.utc).replace(microsecond=0)
limit = datetime.timedelta(hours=23)


def offset_for(clock, weekday_only):
    best = None
    for days in range(-2, 3):
        day = (now + datetime.timedelta(days=days)).date()
        if weekday_only and day.weekday() >= 5:
            continue
        local = datetime.datetime.combine(day, clock, tzinfo=datetime.timezone.utc)
        offset = local - now
        if abs(offset) < limit and (best is None or abs(offset) < abs(best)):
            best = offset
    return best


for spec in sys.argv[2:]:
    name, clock, kind = spec.split(',')
    offset = offset_for(datetime.time.fromisoformat(clock), kind == 'weekday')
    if offset is not None:
        break
else:
    raise SystemExit('no reachable local time')
seconds = int(offset.total_seconds())
text = '%s%d:%02d:%02d' % ('-' if seconds < 0 else '', abs(seconds) // 3600,
                           abs(seconds) // 60 % 60, abs(seconds) % 60)
with tempfile.TemporaryDirectory() as work:
    source = os.path.join(work, 'zone')
    with open(source, 'w') as stream:
        stream.write('Zone SudoIt/Approval %s - SIT\n' % text)
    subprocess.run(['zic', '-d', directory, source], check=True)
print(name, os.path.join(directory, 'SudoIt/Approval'))
PY
chmod 0644 "$WORK/fault-seccomp.py" "$WORK/fault-audit.py" "$WORK/fault-zone.py"
FAULT_LOCALTIME=$(readlink /etc/localtime)

fault_snippet() {
  cat >"$WORK/fault-snippet"
  chmod 0644 "$WORK/fault-snippet"
}

fault_policy() {
  printf '%s\n' "$@" >/etc/sudoers.d/zz-fault
  chmod 0440 /etc/sudoers.d/zz-fault
}

fault_exec() {
  local user=$1 binary=$2 home
  shift 2
  home=$(getent passwd "$user" | cut -d: -f6)
  if [[ $# -gt 0 ]]; then
    run root "python3 '$WORK/fault-seccomp.py' $* -- setpriv --reuid=$user --regid=$(gid_of "$user") --init-groups -- env -i HOME='$home' USER=$user LOGNAME=$user SHELL=/bin/bash PATH='$USER_PATH' LANG=C.UTF-8 S='$binary' /bin/sh -c 'cd \"\$HOME\" && . \"$WORK/fault-snippet\"'"
  else
    run "$user" "S='$binary'; . '$WORK/fault-snippet'"
  fi
}

fault_compare() {
  local setup=$1 check=$2 user=$3
  shift 3
  $setup reference
  fault_exec "$user" /usr/bin/sudo.ws "$@"
  REF_RC=$RC REF_OUT=${OUT//sudo.ws/sudo} REF_ERR=${ERR//sudo.ws/sudo}
  REF_STATE=$($check)
  $setup implementation
  fault_exec "$user" /usr/bin/sudo "$@"
  OUT=${OUT//sudo.ws/sudo} ERR=${ERR//sudo.ws/sudo}
  STATE=$($check)
  printf -- '--- reference state:\n%s\n--- implementation state:\n%s\n' "$REF_STATE" "$STATE" >>"$LOG"
  [[ $RC == "$REF_RC" ]] || fail "exit status: sudo.ws $REF_RC, implementation $RC"
  [[ $OUT == "$REF_OUT" ]] || fail "stdout differs; sudo.ws: [$REF_OUT]"
  [[ $ERR == "$REF_ERR" ]] || fail "stderr differs; sudo.ws: [$REF_ERR]"
  [[ $STATE == "$REF_STATE" ]] || fail "observed state differs; sudo.ws: [$REF_STATE]; implementation: [$STATE]"
}

fault_pty_compare() {
  local setup=$1 user=$2 command=$3 projection=$4
  shift 4
  $setup reference
  pty "$user" "S=/usr/bin/sudo.ws; $command" "$@"
  REF_RC=$RC REF_OUT=$($projection <<<"${OUT//sudo.ws/sudo}")
  $setup implementation
  pty "$user" "S=/usr/bin/sudo; $command" "$@"
  OUT=$($projection <<<"${OUT//sudo.ws/sudo}")
  [[ $RC == "$REF_RC" ]] || fail "exit status: sudo.ws $REF_RC, implementation $RC"
  [[ $OUT == "$REF_OUT" ]] || fail "terminal output differs; sudo.ws: [$REF_OUT]; implementation: [$OUT]"
}

fault_after_prompt() { sed 1d; }

fault_descriptor_probe() {
  fault_snippet <<EOF
exec 5</etc/hostname 7</etc/hostname 9</etc/hostname
"\$S" -n $1 /bin/sh -c 'for fd in 3 4 5 6 7 8 9; do [ -e /proc/\$\$/fd/\$fd ] && echo "open \$fd"; done; echo probe-done'
EOF
}

begin fault-close-range-enosys-default-closefrom && {
  fault_policy 'ivan ALL=(ALL) NOPASSWD: ALL'
  fault_descriptor_probe ''
  fault_compare : : ivan --close-range
  expect_rc 0
  expect_out_line probe-done
  expect_out_lacks 'open'
  end
}

begin fault-close-range-enosys-closefrom-override && {
  fault_policy 'Defaults closefrom_override' 'ivan ALL=(ALL) NOPASSWD: ALL'
  fault_descriptor_probe '-C 8'
  fault_compare : : ivan --close-range
  expect_rc 0
  expect_out_line 'open 5'
  expect_out_line 'open 7'
  expect_out_lacks 'open 9'
  end
}

begin fault-close-range-enosys-without-pty && {
  fault_policy 'Defaults !use_pty, closefrom_override' 'ivan ALL=(ALL) NOPASSWD: ALL'
  fault_descriptor_probe '-C 6'
  fault_compare : : ivan --close-range
  expect_rc 0
  expect_out_line 'open 5'
  expect_out_lacks 'open 7'
  end
}

fault_mail_reset() { rm -f /var/mail/root; }
fault_mail_state() {
  python3 - <<'PY'
import pathlib
import time
mail = pathlib.Path('/var/mail/root')
deadline = time.monotonic() + 10
while time.monotonic() < deadline:
    if mail.exists() and 'COMMAND=/usr/bin/id' in mail.read_text():
        break
    time.sleep(.05)
if not mail.exists():
    print('no mail delivered')
else:
    for line in mail.read_text().splitlines():
        if line.startswith(('To:', 'Subject:', 'Auto-Submitted:')) or 'COMMAND=' in line:
            print(line.split(' : ', 2)[-1] if 'COMMAND=' in line else line)
PY
}

begin fault-close-range-enosys-mailer && {
  fault_policy 'Defaults mail_no_perms, mailerpath=/usr/sbin/sendmail, mailto=admin@example.test, mailsub="fault mail %h"' 'Defaults:ivan !authenticate' 'ivan ALL=(ALL) NOPASSWD: /usr/bin/true'
  fault_snippet <<'EOF'
"$S" -n /usr/bin/id
EOF
  fault_compare fault_mail_reset fault_mail_state ivan --close-range
  expect_rc 1
  expect_err_has "is not allowed to execute '/usr/bin/id' as root"
  grep -qF 'COMMAND=/usr/bin/id' <<<"$STATE" || fail 'denial mail was not delivered'
  rm -f /var/mail/root
  end
}

begin fault-close-range-enosys-askpass && {
  install -m 0755 /dev/stdin "$WORK/fault-askpass" <<'EOF'
#!/bin/sh
printf 'kate''pw\n'
EOF
  fault_policy 'Defaults:kate lecture=never, passwd_tries=1' 'kate ALL=(ALL) ALL'
  fault_snippet <<EOF
SUDO_ASKPASS='$WORK/fault-askpass' "\$S" -A -k /usr/bin/id -u
EOF
  fault_compare : : kate --close-range
  expect_rc 0
  expect_out_line 0
  end
}

fault_rlimit_probe() {
  fault_snippet <<'EOF'
"$S" -n /bin/bash -c 'printf "core=%s locks=%s nproc=%s\n" "$(ulimit -c)" "$(ulimit -x)" "$(ulimit -u)"'
EOF
}

begin fault-rlimit-policy-locks-warning && {
  fault_policy 'Defaults rlimit_locks=100' 'ivan ALL=(ALL) NOPASSWD: ALL'
  fault_rlimit_probe
  fault_compare : : ivan --rlimit=locks
  expect_rc 0
  expect_err_has 'sudo: setrlimit(rlimit_locks): Operation not permitted'
  expect_out_has 'locks=unlimited'
  end
}

begin fault-rlimit-nproc-warnings && {
  fault_policy 'ivan ALL=(ALL) NOPASSWD: ALL'
  fault_rlimit_probe
  fault_compare : : ivan --rlimit=nproc
  expect_rc 0
  expect_err_has 'sudo: setrlimit(RLIMIT_NPROC): Operation not permitted'
  end
}

begin fault-rlimit-core-warning && {
  fault_policy 'ivan ALL=(ALL) NOPASSWD: ALL'
  fault_rlimit_probe
  fault_compare : : ivan --rlimit=core
  expect_rc 0
  expect_err_has 'sudo: setrlimit(RLIMIT_CORE): Operation not permitted'
  end
}

FAULT_NEW_PASSWORD='Qv7#Lm2x!Tz9'
fault_shadow_expire() {
  cp -p "$WORK/fault-shadow" /etc/shadow
  chage -d 0 kate
}

begin fault-pam-expired-password-change && {
  cp -p /etc/shadow "$WORK/fault-shadow"
  fault_policy 'Defaults:kate lecture=never, timestamp_timeout=0' 'kate ALL=(ALL) ALL'
  fault_pty_compare fault_shadow_expire kate \
    "\"\$S\" /usr/bin/id -u && printf '%s\\n' '$FAULT_NEW_PASSWORD' | \"\$S\" -S -k /usr/bin/id -u" cat \
    -e 'password for kate:' -s 'katepw\r' -e 'Current password: ' -s 'katepw\r' \
    -e 'New password: ' -s "$FAULT_NEW_PASSWORD\\r" -e 'Retype new password: ' -s "$FAULT_NEW_PASSWORD\\r"
  expect_rc 0
  expect_out_has 'Account or password is expired, reset your password and try again'
  [[ $(grep -cE '(^|password for kate: )0$' <<<"$OUT") == 2 ]] || fail 'changed password did not authenticate the second command'
  [[ $(getent shadow kate | cut -d: -f3) != 0 ]] || fail 'password change was not recorded'
  cp -p "$WORK/fault-shadow" /etc/shadow
  end
}

begin fault-pam-expired-password-change-mismatch && {
  cp -p /etc/shadow "$WORK/fault-shadow"
  fault_policy 'Defaults:kate lecture=never, timestamp_timeout=0' 'kate ALL=(ALL) ALL'
  fault_pty_compare fault_shadow_expire kate '"$S" /usr/bin/id -u' cat \
    -e 'password for kate:' -s 'katepw\r' -e 'Current password: ' -s 'katepw\r' \
    -e 'New password: ' -s "$FAULT_NEW_PASSWORD\\r" -e 'Retype new password: ' -s 'Wr0ng#Retype\r' \
    -e 'New password: ' -s "$FAULT_NEW_PASSWORD\\r" -e 'Retype new password: ' -s 'Wr0ng#Retype\r' \
    -e 'New password: ' -s "$FAULT_NEW_PASSWORD\\r" -e 'Retype new password: ' -s 'Wr0ng#Retype\r'
  expect_rc 1
  expect_out_has 'sudo: unable to change expired password: Have exhausted maximum number of retries for service'
  [[ $(getent shadow kate | cut -d: -f3) == 0 ]] || fail 'failed password change altered the account'
  cp -p "$WORK/fault-shadow" /etc/shadow
  end
}

fault_feedback_policy() {
  fault_policy 'Defaults:kate lecture=never, pwfeedback, passwd_tries=1' 'kate ALL=(ALL) ALL'
}

begin fault-pwfeedback-erase && {
  fault_feedback_policy
  fault_pty_compare : kate '"$S" -k /usr/bin/id -u' fault_after_prompt -e 'password for kate:' -s $'katepX\x7fw\r'
  expect_rc 0
  expect_out_line 0
  end
}

begin fault-pwfeedback-kill && {
  fault_feedback_policy
  fault_pty_compare : kate '"$S" -k /usr/bin/id -u' fault_after_prompt -e 'password for kate:' -s $'wrong\x15katepw\r'
  expect_rc 0
  expect_out_line 0
  end
}

begin fault-pwfeedback-eof-terminates && {
  fault_feedback_policy
  fault_pty_compare : kate '"$S" -k /usr/bin/id -u' fault_after_prompt -e 'password for kate:' -s $'katepw\x04'
  expect_rc 0
  expect_out_line 0
  end
}

begin fault-pwfeedback-multibyte-erase && {
  fault_feedback_policy
  fault_pty_compare : kate '"$S" -k /usr/bin/id -u' fault_after_prompt -e 'password for kate:' -s $'katep\xc3\xa9\x7fw\r'
  end
}

begin fault-pwfeedback-terminal-transcript && {
  fault_feedback_policy
  fault_pty_compare : kate '"$S" -k /usr/bin/id -u' cat -e 'password for kate:' -s $'wrong\x15katepX\x7fw\r'
  expect_rc 0
  end
}

fault_audit_reset() { rm -f "$PH_DIR/audit.json"; }
fault_audit_state() { python3 "$WORK/fault-audit.py" "$PH_DIR/audit.json"; }

for fault_mode in intercept log_subcmds; do
  begin "fault-audit-json-$fault_mode-subcommands" && {
    plugin_host_setup
    plugin_host_add audit_json "audit_json.so logfile=$PH_DIR/audit.json"
    fault_policy "Defaults $fault_mode"
    fault_snippet <<'EOF'
"$S" -n /bin/sh -c '/usr/bin/id -u; /bin/echo subcommand'
EOF
    fault_compare fault_audit_reset fault_audit_state ivan
    expect_rc 0
    expect_out_line subcommand
    fault_count=1
    [[ $fault_mode == intercept ]] && fault_count=3
    [[ $(grep -c '"plugin_name": "sudoers_policy"' <<<"$STATE") == "$fault_count" ]] || fail "expected $fault_count audited policy acceptances"
    plugin_host_end
  }
done

begin fault-audit-json-list-and-validate && {
  plugin_host_setup
  plugin_host_add audit_json "audit_json.so logfile=$PH_DIR/audit.json"
  fault_snippet <<'EOF'
"$S" -n -l /usr/bin/id; echo "list=$?"
"$S" -n -v; echo "validate=$?"
EOF
  fault_compare fault_audit_reset fault_audit_state ivan
  expect_out_line 'list=0'
  expect_out_line 'validate=0'
  [[ $(grep -c '^  "accept",$' <<<"$STATE") == 2 ]] || fail 'expected two audited acceptances'
  grep -qF '"validate"' <<<"$STATE" || fail 'validation acceptance was not audited'
  plugin_host_end
}

for fault_user in ivan bob; do
  begin "fault-audit-json-unwritable-log-$fault_user" && {
    plugin_host_setup
    printf 'Defaults:bob !authenticate\n' >>/etc/sudoers.d/plugin-host
    plugin_host_add audit_json 'audit_json.so logfile=/dev/full'
    fault_snippet <<'EOF'
"$S" -n /usr/bin/id -u
EOF
    fault_compare : : "$fault_user"
    expect_rc 1
    expect_out_empty
    expect_err_has 'audit_json: unable to log'
    plugin_host_end
  }
done

fault_var_tmp_file() {
  [[ -d /var/tmp ]] && mv /var/tmp "$WORK/fault-var-tmp"
  : >/var/tmp
}
fault_var_tmp_restore() {
  rm -f /var/tmp
  mv "$WORK/fault-var-tmp" /var/tmp
}

begin fault-plugin-io-open-declines && {
  plugin_host_setup
  plugin_host_add sample_io "$PH_SO"
  fault_var_tmp_file
  fault_snippet <<'EOF'
"$S" -n /usr/bin/id -u
EOF
  fault_compare : : ivan
  fault_var_tmp_restore
  expect_rc 0
  expect_out_line 0
  plugin_host_end
}

fault_zone() {
  local branch zone
  rm -rf /usr/share/zoneinfo/SudoIt
  read -r branch zone < <(python3 "$WORK/fault-zone.py" /usr/share/zoneinfo "$@")
  ln -sfn "$zone" /etc/localtime
  printf -- '--- approval local time branch %s: %s\n' "$branch" "$(date)" >>"$LOG"
}
fault_zone_restore() {
  ln -sfn "$FAULT_LOCALTIME" /etc/localtime
  rm -rf /usr/share/zoneinfo/SudoIt
}
fault_approval_night() {
  fault_audit_reset
  fault_zone night,03:00:00,any
}
fault_approval_boundary() {
  fault_audit_reset
  fault_zone boundary,17:00:50,weekday business,12:00:00,weekday night,03:00:00,any
}

begin fault-approval-outside-business-hours && {
  plugin_host_setup
  plugin_host_add sample_approval /opt/sudo-it/plugins/sample_approval.so
  plugin_host_add audit_json "audit_json.so logfile=$PH_DIR/audit.json"
  fault_snippet <<'EOF'
"$S" -n /usr/bin/id -u
EOF
  fault_compare fault_approval_night fault_audit_state ivan
  fault_zone_restore
  expect_rc 1
  expect_out_empty
  expect_err_has 'You are not allowed to use sudo outside business hours'
  grep -qF '"plugin_type": "approval"' <<<"$STATE" || fail 'approval rejection was not audited'
  plugin_host_end
}

begin fault-approval-intercepted-subcommands && {
  plugin_host_setup
  plugin_host_add sample_approval /opt/sudo-it/plugins/sample_approval.so
  plugin_host_add audit_json "audit_json.so logfile=$PH_DIR/audit.json"
  fault_policy 'Defaults intercept'
  fault_snippet <<'EOF'
"$S" -n /bin/sh -c '/usr/bin/id -u; /usr/bin/sleep 15; /bin/echo subcommand; echo "status=$?"'
EOF
  fault_compare fault_approval_boundary fault_audit_state ivan
  fault_zone_restore
  plugin_host_end
}

fault_logsrv_stop() {
  kill "$LSRV_PID" 2>/dev/null
  wait "$LSRV_PID" 2>/dev/null
  cat "$LSRV/daemon.out" >>"$LOG" 2>/dev/null
}

fault_logsrv_tls() {
  logsrv_start '(tls)' || return 1
  openssl genrsa -out "$LSRV/other.key" 2048 >/dev/null 2>&1
  printf 'not a certificate\n' >"$LSRV/garbage.pem"
  logsrv_policy 'localhost:30343(tls)' "Defaults $1"
  fault_snippet <<'EOF'
"$S" -n /bin/echo remote-output
EOF
  fault_compare : : alice
  fault_logsrv_stop
}

begin fault-logsrv-tls-missing-ca-bundle && {
  fault_logsrv_tls "log_server_cabundle=\"$WORK/logsrv-$NUM/missing.pem\""
  expect_rc 0
  expect_out_line remote-output
  expect_err_has 'unable to connect to log server'
  end
}

begin fault-logsrv-tls-invalid-ca-bundle && {
  fault_logsrv_tls "log_server_cabundle=\"$WORK/logsrv-$NUM/garbage.pem\""
  expect_rc 0
  expect_err_has 'unable to connect to log server'
  end
}

begin fault-logsrv-tls-missing-certificate && {
  fault_logsrv_tls "log_server_cabundle=\"$WORK/logsrv-$NUM/ca.pem\", log_server_peer_cert=\"$WORK/logsrv-$NUM/missing.pem\""
  expect_rc 0
  expect_err_has 'unable to connect to log server'
  end
}

begin fault-logsrv-tls-key-mismatch-iolog-refuses && {
  fault_logsrv_tls "log_output, log_server_cabundle=\"$WORK/logsrv-$NUM/ca.pem\", log_server_peer_cert=\"$WORK/logsrv-$NUM/server.pem\", log_server_peer_key=\"$WORK/logsrv-$NUM/other.key\""
  expect_rc 1
  expect_out_empty
  expect_err_has 'unable to connect to log server'
  end
}

begin fault-logsrv-unresolvable-host && {
  logsrv_policy 'logsrv.invalid:30343'
  fault_snippet <<'EOF'
"$S" -n /bin/echo remote-output
EOF
  fault_compare : : alice
  expect_rc 0
  expect_out_line remote-output
  expect_err_has 'unable to connect to log server'
  end
}

fault_remote_reset() { rm -rf "${LSRV:?}/io"/*; }
fault_remote_state() {
  sleep 1
  find "$LSRV/io" -name log.json | wc -l
  find "$LSRV/io" -name stdout -exec cat {} +
}

begin fault-plugin-sudoers-io-with-options-log-server && {
  plugin_host_setup
  plugin_host_add sudoers_io 'sudoers.so iolog_flush=true'
  logsrv_start
  logsrv_policy 127.0.0.1:30343 'Defaults log_output'
  fault_snippet <<'EOF'
"$S" -n /bin/echo remote-output
EOF
  fault_compare fault_remote_reset fault_remote_state alice
  fault_logsrv_stop
  expect_rc 0
  expect_out_line remote-output
  [[ $(head -n 1 <<<"$STATE") == 1 ]] || fail "expected one remote I/O log session, found $(head -n 1 <<<"$STATE")"
  plugin_host_end
}

fault_timestamp_dir=$WORK/fault-ts
fault_timestamp_case=
fault_timestamp_reset() {
  local record
  rm -rf "$fault_timestamp_dir"
  install -d -m 0755 "$fault_timestamp_dir"
  FAULT_TS=$fault_timestamp_dir/ts
  record=$FAULT_TS/$(uid_of kate)
  case $fault_timestamp_case in
    dir-not-directory) : >"$fault_timestamp_dir/file"; FAULT_TS=$fault_timestamp_dir/file/ts ;;
    dir-user-owned) install -d -o kate -m 0700 "$FAULT_TS" ;;
    dir-world-writable) install -d -m 0777 "$FAULT_TS" ;;
    dir-group-writable) install -d -g ivan -m 0770 "$FAULT_TS" ;;
    record-directory) install -d -m 0700 "$FAULT_TS" "$record" ;;
    record-fifo) install -d -m 0700 "$FAULT_TS"; mkfifo -m 0600 "$record" ;;
    record-misaligned) install -d -m 0700 "$FAULT_TS"; printf x >"$record"; chmod 0600 "$record" ;;
    record-zero-filled) install -d -m 0700 "$FAULT_TS"; head -c 100000 /dev/zero >"$record"; chmod 0600 "$record" ;;
  esac
  fault_policy "Defaults:kate lecture=never, timestamp_type=global, timestampdir=$FAULT_TS" 'kate ALL=(ALL) ALL'
}
fault_timestamp_state() {
  find "$fault_timestamp_dir" -mindepth 1 -printf '%P %y %m %u %s\n' | sort
}

for fault_timestamp_case in dir-not-directory dir-user-owned dir-world-writable dir-group-writable record-directory record-fifo record-misaligned record-zero-filled; do
  begin "fault-timestamp-$fault_timestamp_case" && {
    fault_snippet <<'EOF'
"$S" -n /usr/bin/id -u; echo "before=$?"
printf 'katepw\n' | "$S" -S /usr/bin/id -u; echo "authenticated=$?"
"$S" -n /usr/bin/id -u; echo "after=$?"
EOF
    fault_compare fault_timestamp_reset fault_timestamp_state kate
    expect_out_line 'before=1'
    expect_out_line 'authenticated=0'
    rm -rf "$fault_timestamp_dir"
    end
  }
done
