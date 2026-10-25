# Non-policy plugins run unchanged in both hosts.  The fixture is compiled in
# Docker build stages against upstream's API 1.22 header, never at test runtime.
# Every selected test saves/restores sudo.conf and owns its log directory.
plugin_host_setup() {
  PH_DIR=$(mktemp -d "$WORK/plugin-host.XXXXXX")
  chmod 0755 "$PH_DIR"
  PH_SO=/opt/sudo-it/plugin-host.so
  if [[ -e /etc/sudo.conf ]]; then cp -a /etc/sudo.conf "$PH_DIR/sudo.conf.orig"; fi
  printf 'Plugin sudoers_policy sudoers.so\n' >/etc/sudo.conf
  chmod 0644 /etc/sudo.conf
  printf 'Defaults !lecture\nivan ALL=(ALL) NOPASSWD: ALL\n' >/etc/sudoers.d/plugin-host
  chmod 0440 /etc/sudoers.d/plugin-host
}

plugin_host_end() {
  local file
  for file in "$PH_DIR"/*.log "$PH_DIR"/*.json; do
    [[ -f $file ]] || continue
    printf '\n--- plugin file: %s\n' "${file##*/}" >>"$LOG"
    cat "$file" >>"$LOG"
  done
  if [[ -e $PH_DIR/sudo.conf.orig ]]; then
    cp -a "$PH_DIR/sudo.conf.orig" /etc/sudo.conf
  else
    rm -f /etc/sudo.conf
  fi
  rm -f /etc/sudoers.d/plugin-host
  rm -rf "$PH_DIR"
  end
}

plugin_host_add() { printf 'Plugin %s %s\n' "$1" "$2" >>/etc/sudo.conf; }
plugin_host_line() {
  grep -qxF -- "$2" "$PH_DIR/$1" || fail "$1: missing line '$2'"
}
plugin_host_lacks() {
  if [[ -f $PH_DIR/$1 ]] && grep -qF -- "$2" "$PH_DIR/$1"; then
    fail "$1: unexpected '$2'"
  fi
}

# audit_json 1.9.17p2 writes repeated top-level event keys, and Ubuntu's shipped
# DSO incorrectly names values inside arrays. Normalize only that observed
# syntax defect, preserving all pairs so later accepts cannot hide rejections.
plugin_host_json() {
  python3 - "$PH_DIR/audit.json" "$1" "${2:-0}" >>"$LOG" 2>&1 <<'PY'
import json, os, pwd, re, sys, uuid
path, mode, status = sys.argv[1], sys.argv[2], int(sys.argv[3])
with open(path) as stream:
    text = stream.read()
text = re.sub(r'(?m)^(\s+)"(?:submit_argv|submit_envp|run_argv|run_envp)": (?=")', r'\1', text)
pairs = json.loads(text, object_pairs_hook=list)
records = [(kind, dict(record)) for kind, record in pairs]
assert records, 'empty audit document'
for kind, record in records:
    assert kind in ('accept', 'reject', 'error', 'exit'), kind
    # This DSO also groups UUID hex as 10-4-4-4-10 rather than 8-4-4-4-12.
    assert re.fullmatch(r'[0-9a-f]{10}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{10}', record['uuid'])
    uuid.UUID(record['uuid'].replace('-', ''))
    timestamp = dict(record['timestamp'])
    assert type(timestamp['seconds']) is int and timestamp['seconds'] > 0
    assert type(timestamp['nanoseconds']) is int and 0 <= timestamp['nanoseconds'] < 10**9
    assert isinstance(timestamp['iso8601'], str)
    if kind == 'exit':
        continue
    assert record['plugin_name'] and record['plugin_type']
    assert type(record['submit_optind']) is int
    submitted = record['submit_argv']
    assert os.path.basename(submitted[0]) == 'sudo'
    assert submitted[record['submit_optind']].startswith('/'), submitted
    assert all(isinstance(item, str) and '=' in item for item in record['submit_envp'])
    user = dict(record['user_info'])
    expected_user = 'bob' if mode == 'reject' else 'ivan'
    assert user['user'] == expected_user, user
    assert user['uid'] == pwd.getpwnam(expected_user).pw_uid, user
    assert {key for key in user if key.startswith('rlimit_')} == {
        'rlimit_' + key for key in ('as', 'core', 'cpu', 'data', 'fsize', 'locks',
                                   'memlock', 'nofile', 'nproc', 'rss', 'stack')}
    assert dict(record['options'])['noninteractive'] is True
accepts = [record for kind, record in records if kind == 'accept']
rejects = [record for kind, record in records if kind == 'reject']
exits = [record for kind, record in records if kind == 'exit']
if mode == 'reject':
    assert not accepts, 'policy rejection was subsequently accepted'
    assert not exits, 'rejected command has an execution exit record'
    assert any(r['plugin_type'] == 'policy' and r.get('reason') for r in rejects)
elif mode == 'approval-deny':
    assert any(r['plugin_type'] == 'policy' for r in accepts)
    assert not any(r['plugin_type'] == 'approval' for r in accepts)
    assert any(r['plugin_name'] == 'sample_approval' and r['plugin_type'] == 'approval'
               and r['reason'] == 'sample approval denied command name' for r in rejects)
    assert not exits
else:
    count = 2 if mode == 'append' else 1
    policy = [r for r in accepts if r['plugin_type'] == 'policy']
    assert len(policy) == count, records
    assert not rejects and not any(k == 'error' for k, _ in records), records
    assert len(exits) == count, records
    assert len({r['uuid'] for r in policy}) == count
    for record, exited in zip(policy, exits):
        assert record['plugin_name'] == 'sudoers_policy'
        assert record['uuid'] == exited['uuid']
        assert exited['exit_value'] == status, exited
        info = dict(record['command_info'])
        command = '/usr/bin/false' if status else '/usr/bin/id'
        assert info['command'] == command, info
        assert info['runas_uid'] == 0, info
        assert record['run_argv'] == ([command] if status else [command, '-u'])
        assert 'SUDO_USER=ivan' in record['run_envp']
        assert record['submit_argv'][record['submit_optind']:] == record['run_argv']
print('audit JSON structure and event semantics verified')
PY
  [[ $? == 0 ]] || fail 'audit JSON structure/event mismatch (see log)'
}

plugin_host_stream() {
  python3 - "$PH_DIR/io.log" "$1" "$2" >>"$LOG" 2>&1 <<'PY'
from pathlib import Path
import sys
path, name, expected = sys.argv[1:]
prefix = 'io.' + name + '='
chunks = [bytes.fromhex(line[len(prefix):]) for line in Path(path).read_text().splitlines()
          if line.startswith(prefix)]
actual = b''.join(chunks)
assert expected.encode() in actual, (name, actual, expected)
PY
  [[ $? == 0 ]] || fail "IO $1 callback data mismatch (see log)"
}

begin 'plugin host audit JSON acceptance structure' && {
  plugin_host_setup
  plugin_host_add audit_json "audit_json.so logfile=$PH_DIR/audit.json"
  run ivan 'sudo -n /usr/bin/id -u'
  expect_rc 0; expect_out_line 0
  plugin_host_json accept
  [[ $(stat -c %a "$PH_DIR/audit.json") == 600 ]] || fail 'audit logfile mode is not 0600'
  plugin_host_end
}

begin 'plugin host audit JSON nonzero close status' && {
  plugin_host_setup
  plugin_host_add audit_json "audit_json.so logfile=$PH_DIR/audit.json"
  run ivan 'sudo -n /usr/bin/false'
  expect_rc 1; expect_out_empty
  plugin_host_json accept 1
  plugin_host_end
}

begin 'plugin host audit JSON append preserves invocations' && {
  plugin_host_setup
  plugin_host_add audit_json "audit_json.so logfile=$PH_DIR/audit.json"
  run ivan 'sudo -n /usr/bin/id -u && sudo -n /usr/bin/id -u'
  expect_rc 0
  plugin_host_json append
  plugin_host_end
}

begin 'plugin host rejected policy never approved' && {
  plugin_host_setup
  printf 'Defaults:bob !authenticate\n' >>/etc/sudoers.d/plugin-host
  plugin_host_add audit_json "audit_json.so logfile=$PH_DIR/audit.json"
  plugin_host_add sample_approval "$PH_SO log=$PH_DIR/approval.log deny=false"
  plugin_host_add sample_io "$PH_SO log=$PH_DIR/io.log"
  run bob 'sudo -n /usr/bin/id -u'
  expect_rc 1; expect_out_empty
  plugin_host_json reject
  [[ ! -e $PH_DIR/approval.log ]] || fail 'approval opened for a rejected policy decision'
  [[ ! -e $PH_DIR/io.log ]] || fail 'IO opened for a rejected policy decision'
  plugin_host_end
}

begin 'plugin host authentication errors never reach approval' && {
  plugin_host_setup
  plugin_host_add sample_audit "$PH_SO log=$PH_DIR/audit.log"
  plugin_host_add sample_approval "$PH_SO log=$PH_DIR/approval.log"
  run bob 'sudo -n /usr/bin/id -u'
  expect_rc 1; expect_out_empty
  plugin_host_line audit.log 'audit.error name=sudoers_policy type=1 reason=authentication failure'
  plugin_host_lacks audit.log 'audit.accept name='
  [[ ! -e $PH_DIR/approval.log ]] || fail 'approval opened after authentication error'
  plugin_host_end
}

begin 'plugin host sample approval allows other command names' && {
  plugin_host_setup
  plugin_host_add sample_approval "$PH_SO log=$PH_DIR/approval.log deny=false token=approval-options"
  run ivan 'sudo -n /usr/bin/id -u'
  expect_rc 0; expect_out_line 0
  plugin_host_line approval.log 'approval.open'
  plugin_host_line approval.log 'approval.check'
  plugin_host_line approval.log 'approval.close'
  plugin_host_line approval.log 'api=65558'
  plugin_host_line approval.log 'option=deny=false'
  plugin_host_line approval.log 'option=token=approval-options'
  plugin_host_line approval.log 'command_info=command=/usr/bin/id'
  plugin_host_line approval.log 'run=/usr/bin/id'
  plugin_host_line approval.log 'run=-u'
  plugin_host_line approval.log 'run_env=SUDO_USER=ivan'
  plugin_host_end
}

begin 'plugin host sample approval denies command name before IO' && {
  plugin_host_setup
  plugin_host_add audit_json "audit_json.so logfile=$PH_DIR/audit.json"
  plugin_host_add sample_approval "$PH_SO log=$PH_DIR/approval.log deny=touch"
  plugin_host_add sample_io "$PH_SO log=$PH_DIR/io.log"
  run ivan "sudo -n /usr/bin/touch '$PH_DIR/must-not-exist'"
  expect_rc 1; expect_out_empty
  expect_err_has 'sample approval denied command name'
  [[ ! -e $PH_DIR/must-not-exist ]] || fail 'approval-denied command ran'
  [[ ! -e $PH_DIR/io.log ]] || fail 'IO opened after approval rejection'
  plugin_host_line approval.log 'approval.check'
  plugin_host_line approval.log 'approval.close'
  plugin_host_json approval-deny
  plugin_host_end
}

begin 'plugin host audit options and front-end acceptance' && {
  plugin_host_setup
  plugin_host_add sample_audit "$PH_SO log=$PH_DIR/audit.log token=audit-options"
  run ivan 'sudo -n /usr/bin/true'
  expect_rc 0
  plugin_host_line audit.log 'option=token=audit-options'
  plugin_host_line audit.log 'api=65558'
  plugin_host_line audit.log 'submit_optind=2'
  plugin_host_line audit.log 'audit.accept name=sudoers_policy type=1'
  plugin_host_line audit.log 'audit.accept name=sudo type=0'
  plugin_host_line audit.log 'audit.close type=1 status=0'
  plugin_host_end
}

begin 'plugin host IO options stream hooks and close' && {
  plugin_host_setup
  plugin_host_add sample_io "$PH_SO log=$PH_DIR/io.log token=io-options"
  run ivan "printf 'plugin input\n' | sudo -n /bin/sh -c 'cat; printf \"plugin error\\n\" >&2; exit 7'"
  expect_rc 7; expect_out_line 'plugin input'; expect_err_has 'plugin error'
  plugin_host_line io.log 'io.open'
  plugin_host_line io.log 'option=token=io-options'
  plugin_host_line io.log 'io.hooks.version=65536'
  plugin_host_line io.log 'io.close status=1792 error=0'
  plugin_host_stream stdin 'plugin input'
  plugin_host_stream stdout 'plugin input'
  plugin_host_stream stderr 'plugin error'
  plugin_host_end
}

begin 'plugin host IO hooks preserve binary buffers' && {
  plugin_host_setup
  plugin_host_add sample_io "$PH_SO log=$PH_DIR/io.log"
  touch "$PH_DIR/binary.out"
  chmod 0666 "$PH_DIR/binary.out"
  run ivan "printf 'A\\000B\\n' | sudo -n /usr/bin/cat >'$PH_DIR/binary.out'"
  expect_rc 0; expect_out_empty
  python3 - "$PH_DIR" >>"$LOG" 2>&1 <<'PY'
from pathlib import Path
import sys
directory = Path(sys.argv[1])
expected = b'A\0B\n'
assert (directory / 'binary.out').read_bytes() == expected
lines = (directory / 'io.log').read_text().splitlines()
for stream in ('stdin', 'stdout'):
    prefix = 'io.' + stream + '='
    data = b''.join(bytes.fromhex(line[len(prefix):]) for line in lines if line.startswith(prefix))
    assert data == expected, (stream, data)
assert lines.count('io.close status=0 error=0') == 1
PY
  [[ $? == 0 ]] || fail 'IO callbacks lost binary bytes or close count (see log)'
  plugin_host_end
}

begin 'plugin host IO terminal hooks' && {
  plugin_host_setup
  plugin_host_add sample_io "$PH_SO log=$PH_DIR/io.log"
  pty ivan "sudo -n /bin/sh -c 'printf \"plugin-ready: \"; read answer; printf \"plugin-reply=%s\\n\" \"\$answer\"'" \
    -e 'plugin-ready: ' -s 'terminal-input\r'
  expect_rc 0; expect_out_has 'plugin-reply=terminal-input'
  plugin_host_stream ttyin 'terminal-input'
  plugin_host_stream ttyout 'plugin-reply=terminal-input'
  plugin_host_line io.log 'io.close status=0 error=0'
  plugin_host_end
}

begin 'plugin host IO disabled open does not close or log' && {
  plugin_host_setup
  plugin_host_add sample_io "$PH_SO log=$PH_DIR/io.log open=disable"
  run ivan 'sudo -n /usr/bin/id -u'
  expect_rc 0; expect_out_line 0
  plugin_host_line io.log 'io.disabled'
  plugin_host_lacks io.log 'io.close'
  plugin_host_lacks io.log 'io.stdout='
  plugin_host_end
}

begin 'plugin host IO initialization error prevents execution' && {
  plugin_host_setup
  plugin_host_add sample_audit "$PH_SO log=$PH_DIR/audit.log"
  plugin_host_add sample_io "$PH_SO log=$PH_DIR/io.log open=error"
  run ivan "sudo -n /usr/bin/touch '$PH_DIR/must-not-exist'"
  expect_rc 1; expect_out_empty
  expect_err_has 'error initializing I/O plugin sample_io'
  [[ ! -e $PH_DIR/must-not-exist ]] || fail 'command ran after IO initialization error'
  plugin_host_line audit.log 'audit.error name=sample_io type=2 reason=fixture IO open failed'
  plugin_host_lacks audit.log 'audit.accept name=sudo type=0'
  plugin_host_lacks io.log 'io.close'
  plugin_host_end
}

begin 'plugin host missing plugin diagnostic' && {
  plugin_host_setup
  plugin_host_add absent_plugin 'plugin-host-missing.so'
  run ivan 'sudo -n /usr/bin/id -u'
  expect_rc 1; expect_out_empty
  expect_err_has 'error in /etc/sudo.conf, line 2 while loading plugin "absent_plugin"'
  expect_err_has 'unable to load /usr/libexec/sudo/plugin-host-missing.so:'
  expect_err_has 'fatal error, unable to load plugins'
  plugin_host_end
}

begin 'plugin host relative plugin_dir and options' && {
  plugin_host_setup
  printf 'Plugin sudoers_policy /usr/libexec/sudo/sudoers.so\nPath plugin_dir /opt/sudo-it/\n' >/etc/sudo.conf
  plugin_host_add sample_approval "plugin-host.so log=$PH_DIR/approval.log token=relative"
  run ivan 'sudo -n /usr/bin/id -u'
  expect_rc 0; expect_out_line 0
  plugin_host_line approval.log 'option=token=relative'
  plugin_host_line approval.log 'approval.check'
  plugin_host_end
}

begin 'plugin host continuation diagnostic physical line' && {
  plugin_host_setup
  printf 'Plugin absent_plugin \\\n plugin-host-missing.so\n' >>/etc/sudo.conf
  run ivan 'sudo -n /usr/bin/id -u'
  expect_rc 1; expect_out_empty
  expect_err_has 'error in /etc/sudo.conf, line 3 while loading plugin "absent_plugin"'
  expect_err_has 'fatal error, unable to load plugins'
  plugin_host_end
}

begin 'plugin host missing symbol diagnostic' && {
  plugin_host_setup
  plugin_host_add absent_symbol "$PH_SO"
  run ivan 'sudo -n /usr/bin/id -u'
  expect_rc 1; expect_out_empty
  expect_err_has 'error in /etc/sudo.conf, line 2 while loading plugin "absent_symbol"'
  expect_err_has "unable to find symbol \"absent_symbol\" in $PH_SO"
  expect_err_has 'fatal error, unable to load plugins'
  plugin_host_end
}

begin 'plugin host incompatible API major diagnostic' && {
  plugin_host_setup
  plugin_host_add bad_version "$PH_SO"
  run ivan 'sudo -n /usr/bin/id -u'
  expect_rc 1; expect_out_empty
  expect_err_has 'error in /etc/sudo.conf, line 2 while loading plugin "bad_version"'
  expect_err_has "incompatible plugin major version 2 (expected 1) found in $PH_SO"
  expect_err_has 'fatal error, unable to load plugins'
  plugin_host_end
}

begin 'plugin host version invokes every plugin' && {
  plugin_host_setup
  plugin_host_add audit_json "audit_json.so logfile=$PH_DIR/audit.json"
  plugin_host_add sample_audit "$PH_SO log=$PH_DIR/audit.log"
  plugin_host_add sample_approval "$PH_SO log=$PH_DIR/approval.log deny=id"
  plugin_host_add sample_io "$PH_SO log=$PH_DIR/io.log"
  run root 'sudo -V'
  expect_rc 0
  expect_out_has 'JSON audit plugin version 1.9.17p2'
  expect_out_line 'fixture audit version 1.22 verbose=1'
  expect_out_line 'fixture approval version 1.22 verbose=1'
  expect_out_line 'fixture IO version 1.22 verbose=1'
  plugin_host_line approval.log 'approval.close'
  plugin_host_lacks approval.log 'approval.check'
  plugin_host_line io.log 'io.close status=0 error=0'
  plugin_host_end
}

begin 'plugin host unprivileged version is not verbose' && {
  plugin_host_setup
  plugin_host_add sample_approval "$PH_SO log=$PH_DIR/approval.log"
  plugin_host_add sample_io "$PH_SO log=$PH_DIR/io.log"
  plugin_host_add sample_audit "$PH_SO log=$PH_DIR/audit.log"
  run ivan 'sudo -V'
  expect_rc 0
  expect_out_line 'fixture approval version 1.22 verbose=0'
  expect_out_line 'fixture IO version 1.22 verbose=0'
  expect_out_line 'fixture audit version 1.22 verbose=0'
  plugin_host_end
}

for plugin_intercept_type in trace dso; do
  begin "plugin host intercept $plugin_intercept_type approval denies subcommand" && {
    plugin_host_setup
    printf 'Defaults intercept, intercept_type=%s, !use_pty\n' "$plugin_intercept_type" >>/etc/sudoers.d/plugin-host
    plugin_host_add sample_audit "$PH_SO log=$PH_DIR/audit.log"
    plugin_host_add sample_approval "$PH_SO log=$PH_DIR/approval.log deny=id"
    plugin_host_add sample_io "$PH_SO log=$PH_DIR/io.log"
    run ivan "sudo -n /bin/sh -c '/usr/bin/id -u'"
    expect_rc 126; expect_out_empty
    expect_err_has 'sample approval denied command name'
    plugin_host_line approval.log 'command_info=command=/usr/bin/id'
    plugin_host_line approval.log 'command_info=runcwd=/home/ivan'
    plugin_host_line audit.log 'audit.reject name=sample_approval type=4 reason=sample approval denied command name'
    plugin_host_line audit.log 'audit.accepts=4'
    [[ $(grep -cx 'io.open' "$PH_DIR/io.log") == 1 ]] || fail 'IO reopened for intercepted command'
    plugin_host_end
  }

  begin "plugin host intercept $plugin_intercept_type approved subcommand preserves audit state" && {
    plugin_host_setup
    printf 'Defaults intercept, intercept_type=%s, !use_pty\n' "$plugin_intercept_type" >>/etc/sudoers.d/plugin-host
    plugin_host_add sample_audit "$PH_SO log=$PH_DIR/audit.log"
    plugin_host_add sample_approval "$PH_SO log=$PH_DIR/approval.log deny=false"
    run ivan "sudo -n /bin/sh -c 'PLUGIN_SUBCMD=value /usr/bin/id -u'"
    expect_rc 0; expect_out_line 0
    plugin_host_line approval.log 'command_info=command=/usr/bin/id'
    plugin_host_line approval.log 'run_env=PLUGIN_SUBCMD=value'
    plugin_host_line audit.log 'audit.accepts=6'
    plugin_host_line audit.log 'audit.command_info=runcwd=/home/ivan'
    plugin_host_end
  }

  begin "plugin host intercept $plugin_intercept_type log-only does not approve" && {
    plugin_host_setup
    printf 'Defaults !intercept, log_subcmds, intercept_type=%s, !use_pty\n' "$plugin_intercept_type" >>/etc/sudoers.d/plugin-host
    plugin_host_add sample_audit "$PH_SO log=$PH_DIR/audit.log"
    plugin_host_add sample_approval "$PH_SO log=$PH_DIR/approval.log deny=id"
    run ivan "sudo -n /bin/sh -c '/usr/bin/id -u'"
    expect_rc 0; expect_out_line 0
    plugin_host_lacks approval.log 'command_info=command=/usr/bin/id'
    plugin_host_line audit.log 'audit.command_info=command=/usr/bin/id'
    plugin_host_line audit.log 'audit.accepts=4'
    plugin_host_end
  }

  begin "plugin host intercept $plugin_intercept_type approval error refuses subcommand" && {
    plugin_host_setup
    printf 'Defaults intercept, intercept_type=%s, !use_pty\n' "$plugin_intercept_type" >>/etc/sudoers.d/plugin-host
    plugin_host_add sample_audit "$PH_SO log=$PH_DIR/audit.log"
    plugin_host_add sample_approval "$PH_SO log=$PH_DIR/approval.log error=id"
    run ivan "sudo -n /bin/sh -c '/usr/bin/id -u'"
    expect_rc 126; expect_out_empty
    expect_err_has 'sample approval check failed'
    plugin_host_line audit.log 'audit.error name=sample_approval type=4 reason=sample approval check failed'
    plugin_host_line audit.log 'audit.accepts=4'
    plugin_host_end
  }

  begin "plugin host intercept $plugin_intercept_type PTY retains one IO session" && {
    plugin_host_setup
    printf 'Defaults intercept, intercept_type=%s, use_pty\n' "$plugin_intercept_type" >>/etc/sudoers.d/plugin-host
    plugin_host_add sample_audit "$PH_SO log=$PH_DIR/audit.log"
    plugin_host_add sample_approval "$PH_SO log=$PH_DIR/approval.log deny=id"
    plugin_host_add sample_io "$PH_SO log=$PH_DIR/io.log"
    pty ivan "sudo -n /bin/sh -c '/usr/bin/id -u'"
    expect_rc 126
    expect_out_has 'sample approval denied command name'
    plugin_host_line audit.log 'audit.accepts=4'
    [[ $(grep -cx 'io.open' "$PH_DIR/io.log") == 1 ]] || fail 'IO reopened for intercepted command'
    plugin_host_end
  }
done

for plugin_line_ending in comment escaped crlf; do
  begin "plugin host config $plugin_line_ending never swallows approval" && {
    plugin_host_setup
    case $plugin_line_ending in
      comment) printf 'Plugin sample_audit %s log=%s/audit.log # see wiki \\\n' "$PH_SO" "$PH_DIR" >>/etc/sudo.conf ;;
      escaped) printf 'Plugin sample_audit %s log=%s/audit.log \\\\\n' "$PH_SO" "$PH_DIR" >>/etc/sudo.conf ;;
      crlf) printf 'Plugin sample_audit %s log=%s/audit.log\r\n' "$PH_SO" "$PH_DIR" >>/etc/sudo.conf ;;
    esac
    plugin_host_add sample_approval "$PH_SO log=$PH_DIR/approval.log deny=id"
    run ivan 'sudo -n /usr/bin/id -u'
    expect_rc 1; expect_out_empty
    expect_err_has 'sample approval denied command name'
    plugin_host_line approval.log 'approval.check'
    plugin_host_line audit.log 'audit.reject name=sample_approval type=4 reason=sample approval denied command name'
    plugin_host_end
  }
done
