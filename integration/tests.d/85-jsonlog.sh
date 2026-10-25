


jsonlog_compare() {
  local format=$1 scenario=$2
  python3 - "$format" "$scenario" <<'PY'
import json, os, pathlib, pwd, re, shutil, subprocess, sys
sys.path.insert(0, '/usr/local/lib')
from sudo_it_logging import Syslog

fmt, scenario = sys.argv[1:]
path = pathlib.Path('/var/log/sudo.json')
policy = pathlib.Path('/etc/sudoers.d/jsonlog')
options = {'noexit': ', !log_exit_status', 'noaccept': ', !log_allowed',
           'iolog': ', log_output, iolog_dir=/var/log/sudo-json-io',
           'authreject': ', authenticate'}.get(scenario, '')
tag = 'PASSWD' if scenario == 'authreject' else 'NOPASSWD'
policy.write_text('Defaults log_format=' + fmt + ', logfile=/var/log/sudo.json, log_exit_status, !authenticate, syslog_maxlen=80' + options + '\n'
                  'ivan ALL=(ALL:ALL) ' + tag + ': ALL, !/usr/bin/id\n')
policy.chmod(0o440)
user = pwd.getpwnam('ivan')
env = dict(HOME=user.pw_dir, USER='ivan', LOGNAME='ivan', SHELL='/bin/bash',
           PATH='/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin', LANG='C.UTF-8')
args = ['/usr/bin/echo', 'quotes" slash\\ line\n tab\t del\x7f é', 'a' * 1000]
if scenario == 'deny': args = ['/usr/bin/id']
if scenario == 'exit': args = ['/bin/sh', '-c', 'exit 7']
if scenario == 'signal': args = ['/bin/sh', '-c', 'kill -TERM $$']
if scenario == 'group': args = ['-g', 'adm', '/usr/bin/true']
if scenario in ('twice', 'noexit', 'noaccept', 'iolog', 'authreject'): args = ['/usr/bin/true']

class Pairs(list): pass
def decode(text): return json.loads(text, object_pairs_hook=Pairs)
def normalize(value, key=''):
    if isinstance(value, Pairs):
        return [(k, normalize(v, k)) for k, v in value]
    if key == 'uuid':
        assert re.fullmatch(r'[0-9a-f]{10}(?:-[0-9a-f]{4}){3}-[0-9a-f]{10}', value), value
        return '<uuid>'
    if key in ('server_time', 'submit_time', 'exit_time', 'alert_time', 'run_time'):
        raise AssertionError('timestamp was not an object')
    if key in ('seconds', 'nanoseconds'):
        assert isinstance(value, int) and value >= 0
        if key == 'nanoseconds': assert value < 1000000000
        return '<time>'
    if key == 'iso8601':
        assert re.fullmatch(r'\d{14}Z', value)
        return '<utc>'
    if key == 'localtime':
        assert re.fullmatch(r'[A-Z][a-z]{2} [ 0-9][0-9] \d\d:\d\d:\d\d', value)
        return '<local>'
    if key in ('runenv', 'submitenv'):

        return sorted(value)
    return value

def execute(binary):
    if scenario == 'iolog': shutil.rmtree('/var/log/sudo-json-io', ignore_errors=True)
    path.unlink(missing_ok=True)
    with Syslog() as logger:
        cmd = ['setpriv', '--reuid=' + str(user.pw_uid), '--regid=' + str(user.pw_gid),
               '--init-groups', '--', binary, '-n'] + args
        result = subprocess.run(cmd, cwd=user.pw_dir, env=env, capture_output=True)
        expected = {'deny': 1, 'authreject': 1, 'exit': 7, 'signal': -15}.get(scenario, 0)
        assert result.returncode == expected, (binary, result.returncode, result.stderr)
        if scenario == 'twice':
            result = subprocess.run(cmd, cwd=user.pw_dir, env=env, capture_output=True)
            assert result.returncode == 0
        messages = logger.messages()
    text = path.read_text()
    if fmt == 'json_compact':
        records = [pair for line in text.splitlines() for pair in decode(line)]
        assert all(line.startswith('{"') for line in text.splitlines())
    else:
        assert text.startswith('{\n    "') and text.endswith('\n}\n'), text
        records = decode(text)
    kinds = [k for k, _ in records]
    expected_kinds = {'noexit': ['accept'], 'noaccept': ['exit'],
                      'deny': ['reject'], 'authreject': ['reject']}.get(
                          scenario, ['accept', 'exit'] * (2 if scenario == 'twice' else 1))
    assert kinds == expected_kinds, kinds
    for i, (kind, fields) in enumerate(records):
        values = dict(fields)
        if kind == 'exit':
            if scenario != 'noaccept': assert values['uuid'] == dict(records[i-1][1])['uuid']
            assert [k for k, _ in fields].count('exit_value') == 2
            assert values['exit_value'] == {'exit': 7, 'signal': 143}.get(scenario, 0)
            if scenario == 'signal': assert values['signal'] == 'TERM' and not values['dumped_core']
        if kind == 'reject': assert values['reason'] == ('a password is required' if scenario == 'authreject' else 'command not allowed')
    cee = [m.split('@cee:', 1)[1] for m in messages if '@cee:' in m]
    assert len(cee) == len(records), (messages, kinds)
    for data, record in zip(cee, records):
        assert '\n' not in data and ' : (command continued)' not in data
        decoded = decode(data)
        assert decoded[0][0] == 'sudo'
        assert normalize(decoded[0][1]) == normalize(Pairs([record]))
    return normalize(Pairs(records))

reference = execute('/usr/bin/sudo.ws')
actual = execute('/usr/bin/sudo')
assert actual == reference, 'JSON mismatch\nreference: ' + repr(reference) + '\nactual: ' + repr(actual)
print('JSON and syslog match sudo.ws')
PY
}

for json_format in json json_compact json_pretty; do
  for json_scenario in allow deny exit signal group twice noexit noaccept iolog authreject; do
    begin "jsonlog-$json_format-$json_scenario" && {
      jsonlog_compare "$json_format" "$json_scenario" >"$WORK/json-result" 2>&1 || fail "$(cat "$WORK/json-result")"
      end
    }
  done
done
