


plugin_host_setup() {
  PH_DIR=$(mktemp -d "$WORK/plugin-host.XXXXXX")
  chmod 0755 "$PH_DIR"
  PH_SO=/opt/sudo-it/plugins/sample_plugin.so
  if [[ -e /etc/sudo.conf ]]; then cp -a /etc/sudo.conf "$PH_DIR/sudo.conf.orig"; fi
  printf 'Plugin sudoers_policy sudoers.so\n' >/etc/sudo.conf
  chmod 0644 /etc/sudo.conf
  printf 'Defaults !lecture\nivan ALL=(ALL) NOPASSWD: ALL\n' >/etc/sudoers.d/plugin-host
  chmod 0440 /etc/sudoers.d/plugin-host
  rm -f /var/tmp/sample-*.input /var/tmp/sample-*.output
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
  rm -f /var/tmp/sample-*.input /var/tmp/sample-*.output
  rm -rf "$PH_DIR"
  end
}

plugin_host_add() { printf 'Plugin %s %s\n' "$1" "$2" >>/etc/sudo.conf; }




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
  plugin_host_add absent_symbol /usr/libexec/sudo/sudoers.so
  run ivan 'sudo -n /usr/bin/id -u'
  expect_rc 1; expect_out_empty
  expect_err_has 'error in /etc/sudo.conf, line 2 while loading plugin "absent_symbol"'
  expect_err_has 'unable to find symbol "absent_symbol" in /usr/libexec/sudo/sudoers.so'
  expect_err_has 'fatal error, unable to load plugins'
  plugin_host_end
}

begin 'plugin host upstream IO binary streams' && {
  plugin_host_setup
  plugin_host_add sample_io "$PH_SO"
  touch "$PH_DIR/binary.out"
  chmod 0666 "$PH_DIR/binary.out"
  run ivan "printf 'A\\000B\\n' | sudo -n /usr/bin/cat >'$PH_DIR/binary.out'"
  expect_rc 0; expect_out_empty
  python3 - "$PH_DIR/binary.out" >>"$LOG" 2>&1 <<'PY'
from pathlib import Path
import sys
expected = b'A\0B\n'
assert Path(sys.argv[1]).read_bytes() == expected
for stream in ('input', 'output'):
    files = list(Path('/var/tmp').glob('sample-*.' + stream))
    assert len(files) == 1, files
    assert files[0].read_bytes() == expected, (stream, files[0].read_bytes())
PY
  [[ $? == 0 ]] || fail 'upstream IO plugin lost binary stream bytes'
  plugin_host_end
}

begin 'plugin host upstream IO terminal streams' && {
  plugin_host_setup
  plugin_host_add sample_io "$PH_SO"
  pty ivan "sudo -n /bin/sh -c 'printf \"plugin-ready: \"; read answer; printf \"plugin-reply=%s\\n\" \"\$answer\"'" \
    -e 'plugin-ready: ' -s 'terminal-input\r'
  expect_rc 0; expect_out_has 'plugin-reply=terminal-input'
  python3 - >>"$LOG" 2>&1 <<'PY'
from pathlib import Path
for stream, expected in [('input', b'terminal-input'), ('output', b'plugin-reply=terminal-input')]:
    files = list(Path('/var/tmp').glob('sample-*.' + stream))
    assert len(files) == 1, files
    assert expected in files[0].read_bytes(), (stream, files[0].read_bytes())
PY
  [[ $? == 0 ]] || fail 'upstream IO plugin lost terminal stream bytes'
  plugin_host_end
}

for plugin_version_user in root ivan; do
  begin "plugin host upstream versions $plugin_version_user" && {
    plugin_host_setup
    plugin_host_add sample_approval /opt/sudo-it/plugins/sample_approval.so
    plugin_host_add sample_io "$PH_SO"
    plugin_host_add audit_json "audit_json.so logfile=$PH_DIR/audit.json"
    run "$plugin_version_user" 'sudo -V'
    expect_rc 0
    expect_out_line 'sample approval plugin version 1.9.17p2'
    expect_out_line 'Sample I/O plugin version 1.9.17p2'
    expect_out_has 'JSON audit plugin version 1.9.17p2'
    [[ -f $PH_DIR/audit.json && ! -s $PH_DIR/audit.json ]] || fail 'version query did not leave an empty audit log'
    plugin_host_end
  }
done

begin 'plugin host audit JSON policy rejection' && {
  plugin_host_setup
  printf 'Defaults:bob !authenticate\n' >>/etc/sudoers.d/plugin-host
  plugin_host_add audit_json "audit_json.so logfile=$PH_DIR/audit.json"
  run bob 'sudo -n /usr/bin/id -u'
  expect_rc 1; expect_out_empty
  plugin_host_json reject
  plugin_host_end
}
