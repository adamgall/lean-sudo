import argparse
import collections
import copy
import difflib
import hashlib
import json
import os
from pathlib import Path
import pwd
import re
import shlex
import shutil
import signal
import subprocess
import sys
import threading
import time

from generate import RECORDER, USERS, empty_state, generate


ROOT = Path('/var/lib/conformance')
LOG = Path('/var/log/conformance.log')
MAIL = Path('/var/mail/root')
SYSLOG = ROOT / 'syslog'
OUT = Path('/out/conformance')
BASELINE = {}
CRASHES = {signal.SIGSEGV, signal.SIGBUS, signal.SIGABRT, signal.SIGILL, signal.SIGFPE,
           signal.SIGSYS, signal.SIGTRAP}
ALIAS_ERROR = re.compile(r'(?:User|Runas|Host|Cmnd)_Alias "[^"]+" referenced but not defined'
                         r'|cycle in (?:User|Runas|Host|Cmnd)_Alias')
ALIAS_LINE = re.compile(r'(?m)^[^\n]*:\d+:\d+: (?:' + ALIAS_ERROR.pattern + r')[^\n]*\n')


def command(argv, **kwargs):
    return subprocess.run(argv, check=True, capture_output=True, **kwargs)


def text(path):
    return path.read_text(errors='backslashreplace') if path.exists() else ''


def put(path, content, mode=0o440):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content)
    path.chmod(mode)


def install(source, target, mode):
    target = Path(target)
    target.unlink(missing_ok=True)
    os.link(source, target)
    os.chown(target, 0, 0)
    target.chmod(mode)


class Logger:
    def __init__(self):
        config = ROOT / 'rsyslog.conf'
        put(config,
            'global(maxMessageSize="256k" parser.escapeControlCharactersOnReceive="off")\n'
            'module(load="imuxsock" SysSock.Name="/dev/log" '
            'SysSock.RateLimit.Interval="0")\n'
            'template(name="raw" type="string" string="%rawmsg%\\n")\n'
            '*.* action(type="omfile" file="' + str(SYSLOG) +
            '" template="raw" flushOnTXEnd="on")\n')
        self.diagnostics = (ROOT / 'rsyslog-errors').open('w')
        self.process = subprocess.Popen(['rsyslogd', '-n', '-i', str(ROOT / 'rsyslog.pid'),
                                         '-f', str(config)], stderr=self.diagnostics)
        self.serial = 0
        self.wait(lambda: Path('/dev/log').is_socket())
        self.drain()
        self.offset = SYSLOG.stat().st_size

    def wait(self, predicate):
        deadline = time.monotonic() + 10
        while not predicate():
            if time.monotonic() >= deadline or self.process.poll() is not None:
                raise RuntimeError('rsyslog failed: ' + text(ROOT / 'rsyslog-errors'))
            time.sleep(.002)

    def drain(self):
        self.serial += 1
        marker = 'conformance-drain-' + str(self.serial)
        offset = SYSLOG.stat().st_size if SYSLOG.exists() else 0
        command(['logger', '--socket', '/dev/log', '--', marker])

        def received():
            if not SYSLOG.exists():
                return False
            with SYSLOG.open(errors='backslashreplace') as stream:
                stream.seek(offset)
                return marker in stream.read()

        self.wait(received)
        return marker

    def start(self):
        self.drain()
        self.offset = SYSLOG.stat().st_size

    def finish(self):
        marker = self.drain()
        with SYSLOG.open(errors='backslashreplace') as stream:
            stream.seek(self.offset)
            records = stream.read().splitlines(keepends=True)
        return ''.join(record for record in records if marker not in record)

    def close(self):
        self.process.terminate()
        self.process.wait(timeout=10)
        self.diagnostics.close()


def normalise(value):
    identities = {}

    def identity(match):
        token = match.group(0)
        if token not in identities:
            identities[token] = '<generated-' + str(len(identities)) + '>'
        return identities[token]

    def visit(item, key=''):
        if isinstance(item, dict):
            return {k: visit(v, k) for k, v in item.items()}
        if isinstance(item, list):
            return [visit(v, key) for v in item]
        if key == 'SUDO_PID':
            return '<pid>'
        if not isinstance(item, str):
            return item
        item = re.sub(r'\b(?:Mon|Tue|Wed|Thu|Fri|Sat|Sun),? '
                      r'\d{1,2} [A-Z][a-z]{2} \d{4} \d\d:\d\d:\d\d [+-]\d{4}',
                      '<date>', item)
        item = re.sub(r'\b(?:Jan|Feb|Mar|Apr|May|Jun|Jul|Aug|Sep|Oct|Nov|Dec) '
                      r'[ 0-9]\d \d\d:\d\d:\d\d(?: \d{4})?', '<time>', item)
        item = re.sub(r'\b\d{4}-\d\d-\d\d[T ]\d\d:\d\d:\d\d'
                      r'(?:\.\d+)?(?:Z|[+-]\d\d:\d\d)?', '<time>', item)
        item = re.sub(r'("(?:seconds|nanoseconds)"\s*:\s*)\d+', r'\1"<time>"', item)
        item = re.sub(r'("iso8601"\s*:\s*")\d{14}Z', r'\1<time>', item)
        item = re.sub(r'\b[0-9a-f]{10}(?:-[0-9a-f]{4}){3}-[0-9a-f]{10}\b',
                      identity, item)
        item = re.sub(r'\b(sudo|unix_chkpwd)\[\d+\]', r'\1[<pid>]', item)
        item = re.sub(r'(?<=pid=)\d+', '<pid>', item)
        item = re.sub(r'(?<=PID=)\d+', '<pid>', item)
        item = re.sub(r'(?<=ppid=)\d+', '<pid>', item)
        item = re.sub(r'(?<=SUDO_PID=)\d+', '<pid>', item)
        item = re.sub(r'(pipe|socket):\[\d+\]', lambda m: m[1] + ':[<inode>]', item)
        item = re.sub(r'/dev/pts/\d+', '/dev/pts/<tty>', item)
        item = re.sub(r'(?<=TTY=)pts/\d+', 'pts/<tty>', item)
        item = re.sub(r'\bE?[0-9A-Za-z]{6}-[0-9A-Za-z]{6,16}-[0-9A-Za-z]{2,4}\b',
                      identity, item)
        item = re.sub(r'(conformance-edit)\.[A-Za-z0-9]{6,}', r'\1.<temporary>', item)
        return item

    return visit(value)


def tracked_roots():
    homes = sorted({pwd.getpwnam(name).pw_dir for name in USERS})
    return ['/run/sudo', '/var/log', '/var/lib/sudo', '/tmp'] + homes


def snapshot():
    entries = {}
    for root in tracked_roots():
        for directory, names, files in os.walk(root):
            for name in [directory] + [os.path.join(directory, n) for n in names + files]:
                try:
                    info = os.lstat(name)
                except FileNotFoundError:
                    continue
                kind = 'd' if os.path.isdir(name) and not os.path.islink(name) else 'f'
                entries[name] = (kind, oct(info.st_mode & 0o7777), info.st_uid, info.st_gid,
                                 0 if kind == 'd' else info.st_size,
                                 0 if kind == 'd' else info.st_mtime_ns)
    return entries


def file_changes(before, after):
    created = [f'{path} {after[path][0]} {after[path][1]} {after[path][2]}:{after[path][3]}'
               for path in sorted(after.keys() - before.keys())]
    modified = [path for path in sorted(after.keys() & before.keys())
                if after[path] != before[path]]
    return dict(created=created, deleted=sorted(before.keys() - after.keys()),
                modified=modified)


def reset(scenario):
    for name in ['/run/sudo', '/var/lib/sudo', '/var/db/sudo', '/etc/sudoers.d',
                 '/etc/conformance.d', '/var/log/sudo-io']:
        shutil.rmtree(name, ignore_errors=True)
    for path in sorted(snapshot().keys() - BASELINE.keys(), reverse=True):
        if os.path.isdir(path) and not os.path.islink(path):
            os.chmod(path, 0o700)
            shutil.rmtree(path, ignore_errors=True)
        else:
            Path(path).unlink(missing_ok=True)
    Path('/etc/sudoers.d').mkdir()
    Path('/etc/conformance-include').unlink(missing_ok=True)
    put('/etc/sudoers', '\n'.join(scenario['lines']) + '\n')
    for path, content in scenario['includes'].items():
        put(path, content)
    for path in (LOG, MAIL):
        path.unlink(missing_ok=True)
    put(ROOT / 'record.json', '', 0o666)
    put('/tmp/conformance-edit', 'original content\n', 0o644)


def processes():
    found = {}
    for entry in os.listdir('/proc'):
        if not entry.isdigit():
            continue
        try:
            stat = Path('/proc', entry, 'stat').read_text()
            cmdline = Path('/proc', entry, 'cmdline').read_bytes()
        except OSError:
            continue
        name, state = stat[stat.index('(') + 1:stat.rindex(')')], stat[stat.rindex(')') + 2]
        if state != 'Z':
            found[int(entry)] = name + ' ' + cmdline.replace(b'\0', b' ').decode(
                errors='backslashreplace').strip()
    return found


def busy(baseline):
    return any(pid not in baseline and command_name.split(' ', 1)[0] in
               ('sudo', 'sudo.ws', 'sendmail', 'exim4')
               for pid, command_name in processes().items())


def settle(baseline):
    deadline = time.monotonic() + 5
    while busy(baseline) and time.monotonic() < deadline:
        time.sleep(.01)
    command(['/usr/sbin/exim4', '-qff'])
    shutil.rmtree('/var/spool/exim4/input', ignore_errors=True)
    Path('/var/spool/exim4/input').mkdir(mode=0o750)
    shutil.chown('/var/spool/exim4/input', 'Debian-exim', 'Debian-exim')
    stray = {pid: name for pid, name in processes().items()
             if pid not in baseline and pid != os.getpid()}
    for pid in stray:
        try:
            os.kill(pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
    return sorted(stray.values())


def front_end(baseline):
    candidates = [pid for pid, name in processes().items()
                  if pid not in baseline and name.split(' ', 1)[0] == 'sudo']
    return min(candidates) if candidates else None


def feed(writer, data):
    try:
        os.write(writer, data)
    except OSError:
        pass
    os.close(writer)


def pending(pid, number):
    bit = 1 << (number - 1)
    try:
        tasks = os.listdir(f'/proc/{pid}/task')
        paths = [Path(f'/proc/{pid}/status')] + [Path(f'/proc/{pid}/task/{t}/status')
                                                 for t in tasks]
        lines = [line for path in paths for line in path.read_text().splitlines()]
    except OSError:
        return False
    return any(int(line.split()[1], 16) & bit for line in lines
               if line.startswith(('SigPnd:', 'ShdPnd:')))


def consumed(pid, number):
    deadline = time.monotonic() + .25
    while pending(pid, number) and time.monotonic() < deadline:
        time.sleep(.001)



def drive(state, writer, data, baseline, started, anchored):
    if not state['hold_stdin']:
        feed(writer, data)
    if anchored:
        deadline = time.monotonic() + 3
        while not text(ROOT / 'record.json') and time.monotonic() < deadline:
            time.sleep(.005)
        started = time.monotonic()
    for delay, name in state['signals']:
        time.sleep(max(0, started + delay - time.monotonic()))
        target = front_end(baseline)
        if target:
            try:
                os.kill(target, getattr(signal, name))
            except ProcessLookupError:
                pass
            consumed(target, getattr(signal, name))
    if state['hold_stdin']:
        time.sleep(.1)
        feed(writer, data)


def execute(scenario, implementation, logger, timeout):
    reset(scenario)
    mode = scenario['mode']
    state = scenario.get('state') or empty_state()
    if mode == 'sudo':
        source = '/opt/impl/sudo' if implementation == 'lean' else '/usr/bin/sudo.ws'
        install(source, '/usr/bin/sudo', 0o4755)
        binary = '/usr/bin/sudo'
    else:
        source = ('/opt/impl/visudo' if implementation == 'lean'
                  else '/usr/sbin/visudo.ws')
        install(source, '/usr/sbin/visudo', 0o755)
        install('/opt/impl/sudo', '/usr/bin/sudo', 0o4755)
        binary = '/usr/sbin/visudo'
    user = pwd.getpwnam(scenario['user'] if mode == 'sudo' else 'root')
    env = dict(HOME=user.pw_dir, USER=user.pw_name, LOGNAME=user.pw_name,
               SHELL=user.pw_shell, PATH='/usr/local/sbin:/usr/local/bin:/usr/sbin:'
               '/usr/bin:/sbin:/bin', LANG='C.UTF-8', TERM='dumb')
    env.update(scenario['env'])
    if mode == 'visudo':
        env['VISUDO_SUDO_BINARY'] = '/opt/impl/sudo'
    spec = dict(user=user.pw_name, argv=[binary] + scenario['argv'],
                env=[k + '=' + v for k, v in env.items()] + state['env_raw'],
                limits=state['limits'], descriptors=state['descriptors'],
                close=state['close'], umask=state['umask'], cwd_state=state['cwd_state'],
                cwd='/tmp/conformance-cwd' if state['cwd_state'] else None,
                drop=not scenario['terminal'])
    put(ROOT / 'launch.json', json.dumps(spec), 0o644)
    launch = ['/usr/bin/python3', str(Path(__file__).with_name('launch.py')),
              str(ROOT / 'launch.json')]
    data = scenario['stdin'].encode()
    if scenario['terminal']:
        snippet = shlex.join(launch) + '; status=$?; stty -a; exit $status'
        argv = ['/opt/sudo-it/ptyrun.py', '-t', str(timeout), user.pw_name, snippet]
        if scenario['stdin']:
            argv += ['-e', 'conformance-password: ', '-s', scenario['stdin']]
        data = b''
    else:
        argv = launch
    before = snapshot()
    baseline = set(processes())
    logger.start()
    reader, writer = os.pipe()
    started = time.monotonic()
    process = subprocess.Popen(argv, cwd='/', env=dict(PATH=env['PATH']), stdin=reader,
                               stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                               start_new_session=True)
    os.close(reader)
    anchored = '--sleep' in scenario['argv'] and not state['hold_stdin']
    if not state['hold_stdin'] and not state['signals']:
        feed(writer, data)
        driver = None
    else:
        driver = threading.Thread(target=drive,
                                  args=(state, writer, data, baseline, started, anchored))
        driver.start()
    timed_out = False
    try:
        stdout, stderr = process.communicate(timeout=timeout + 1)
    except subprocess.TimeoutExpired:
        timed_out = True
        os.killpg(process.pid, signal.SIGKILL)
        stdout, stderr = process.communicate()
    if driver:
        driver.join()
    stray = settle(baseline)
    record = text(ROOT / 'record.json')
    result = dict(status=process.returncode, timed_out=timed_out,
                  stdout=stdout.decode(errors='backslashreplace'),
                  stderr=stderr.decode(errors='backslashreplace'),
                  logfile=text(LOG), syslog=logger.finish(), mail=text(MAIL),
                  record=json.loads(record) if record else None,
                  edited_file=text(Path('/tmp/conformance-edit')),
                  files=file_changes(before, snapshot()), stray=stray)
    return result


def differences(left, right, path=''):
    if isinstance(left, dict) and isinstance(right, dict):
        result = []
        for key in sorted(left.keys() | right.keys()):
            child = path + '.' + key if path else key
            if key not in left or key not in right:
                result.append(child)
            else:
                result.extend(differences(left[key], right[key], child))
        return result
    return [] if left == right else [path]


def invariants(scenario, raw):
    lean, reference = raw['lean'], raw['reference']
    found = []
    status = lean['status']
    terminated = -status if status < 0 else (status - 128 if scenario['terminal'] else 0)
    if terminated in CRASHES:
        found.append('crash')
    if lean['timed_out'] and not reference['timed_out']:
        found.append('timeout')
    if lean['stray']:
        found.append('stray-processes')
    return found


def invalid_utf8(value):
    return any(0xdc80 <= ord(character) <= 0xdcff for character in value)


def without_submitenv_entries(text, entries):
    def array(match):
        items = match.group(2)[1:-1].split('","') if match.group(2) else []
        kept = [item for item in items if item not in entries]
        return match.group(1) + ('"' + '","'.join(kept) + '"' if kept else '') + match.group(3)

    return re.sub(r'("submitenv":\[)([^\]]*)(\])', array, text)


def without_invalid_environment(result, raw_entries):
    logged = {entry.encode('utf-8', 'surrogateescape').decode('utf-8', 'backslashreplace')
              for entry in raw_entries if invalid_utf8(entry)}
    result = dict(result, logfile=without_submitenv_entries(result['logfile'], logged),
                  syslog=without_submitenv_entries(result['syslog'], logged))
    record = result['record']
    if record is None:
        return result
    record = dict(record, environment={k: v for k, v in record['environment'].items()
                                       if not invalid_utf8(k + v)},
                  environ=[entry for entry in record['environ'] if not invalid_utf8(entry)])
    return dict(result, record=record)


def deviation(scenario, lean, reference):
    state = scenario.get('state') or empty_state()
    if any(invalid_utf8(entry) for entry in state['env_raw']):
        if without_invalid_environment(reference, state['env_raw']) == lean:
            return 'non-utf8-environment-dropped'
    if lean['status'] == 0 or lean['record'] is not None:
        return None
    stripped = ALIAS_LINE.sub('', lean['stderr'])
    if stripped != lean['stderr'] and dict(lean, stderr=stripped) == reference:
        return 'fail-closed-alias-resolution'
    lean_output = lean['stderr'] + lean['stdout']
    reference_output = reference['stderr'] + reference['stdout']
    sudo = scenario['mode'] == 'sudo'
    if any(invalid_utf8(argument) for argument in scenario['argv']) and sudo:
        if lean_output and not lean['syslog'] and not lean['logfile']:
            return 'non-utf8-arguments-refused'
    if sudo and 'syntax error' in reference_output and 'syntax error' in lean_output:
        return 'fail-closed-policy-syntax'
    if ALIAS_ERROR.search(lean_output) and 'syntax error' not in reference_output and (
            sudo or reference['status'] == 0):
        return 'fail-closed-alias-resolution'
    if sudo and 'is invalid for option' in lean_output and (
            'is invalid for option' in reference_output):
        return 'fail-closed-default-value'
    return None


def outcome(scenario, raw, normal):
    broken = invariants(scenario, raw)
    if normal['lean'] == normal['reference'] and not broken:
        return 'equal', None
    if not broken:
        rule = deviation(scenario, normal['lean'], normal['reference'])
        if rule:
            return 'deviation', rule
    return 'different', difference_classes(scenario, normal, broken)


def judge(scenario, raw, normal, logger, timeout):
    status, key = outcome(scenario, raw, normal)
    lean = normal['lean']
    state = scenario.get('state') or empty_state()
    if (status != 'different' or 2 not in state['close'] or invariants(scenario, raw)
            or lean['status'] == 0 or lean['record'] is not None):
        return status, key
    companion = copy.deepcopy(scenario)
    companion['state']['close'] = []
    raw, normal = compare(companion, logger, timeout)
    status, rule = outcome(companion, raw, normal)
    return ('deviation', rule) if status == 'deviation' else ('different', key)


def created_paths(entries):
    return {entry.split(' ', 1)[0]: entry for entry in entries}


def difference_classes(scenario, normal, broken):
    lean, reference = normal['lean'], normal['reference']
    prefix = scenario['mode'] + ':'
    if broken:
        lines = (lean['stderr'] + lean['stdout']).splitlines()
        return [prefix + 'invariant=' + name + ':' + (lines[0] if lines else '<no output>')
                for name in broken]
    found = set()
    local = []
    for path in differences(lean, reference):
        if path == 'record.environ' and sorted(lean['record']['environ']) == sorted(
                reference['record']['environ']):
            found.add(prefix + 'record.environ(order)')
        elif path == 'files.created':
            left, right = (created_paths(side['files']['created']) for side in (lean, reference))
            for name in sorted(left.keys() | right.keys()):
                if left.get(name) != right.get(name):
                    found.add(prefix + 'files.created[' + '/'.join(name.split('/')[:4]) + ']')
        elif path.startswith('files.'):
            found.add(prefix + path)
        else:
            local.append(path)
    if local:
        found.add(prefix + scenario['feature'] + ':' + ','.join(local))
    return sorted(found)


def compare(scenario, logger, timeout):
    raw = {side: execute(scenario, side, logger, timeout) for side in ('reference', 'lean')}
    normal = {side: normalise(value) for side, value in raw.items()}
    return raw, normal


def shrink(scenario, expected, logger, timeout, budget):
    current = copy.deepcopy(scenario)
    attempts = 0

    def keeps(trial):
        nonlocal attempts
        attempts += 1
        raw, normal = compare(trial, logger, timeout)
        if any(v['timed_out'] for v in raw.values()) and 'timeout' not in expected:
            return False
        status, found = judge(trial, raw, normal, logger, timeout)
        return status == 'different' and expected in found

    default = empty_state()
    for name in sorted(current['state']):
        if attempts < budget and current['state'][name] != default[name]:
            trial = copy.deepcopy(current)
            trial['state'][name] = default[name]
            if keeps(trial):
                current = trial
    fields = ('lines', 'argv') if scenario['mode'] == 'sudo' else ('lines',)
    for field in fields:
        width = max(1, len(current[field]) // 2)
        while width and attempts < budget:
            changed = False
            for start in range(0, len(current[field]), width):
                trial = copy.deepcopy(current)
                del trial[field][start:start + width]
                if field == 'argv' and not trial[field]:
                    continue
                if keeps(trial):
                    current = trial
                    changed = True
                    break
                if attempts >= budget:
                    break
            if not changed:
                width //= 2
    raw, normal = compare(current, logger, timeout)
    return current, raw, normal, attempts


def save_case(directory, scenario, raw, normal, classification, attempts=0):
    directory.mkdir(parents=True, exist_ok=True)
    data = dict(scenario=scenario, raw=raw, normalised=normal,
                classification=classification, shrink_attempts=attempts)
    put(directory / 'case.json', json.dumps(data, indent=2, ensure_ascii=True) + '\n', 0o644)
    put(directory / 'sudoers', '\n'.join(scenario['lines']) + '\n', 0o644)
    delta = ''.join(difflib.unified_diff(
        json.dumps(normal['reference'], indent=2, sort_keys=True).splitlines(True),
        json.dumps(normal['lean'], indent=2, sort_keys=True).splitlines(True),
        fromfile='sudo.ws', tofile='lean-sudo'))
    put(directory / 'difference.diff', delta, 0o644)


def setup():
    ROOT.mkdir(parents=True, exist_ok=True)
    ROOT.chmod(0o755)
    OUT.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(Path(__file__).with_name('record.py'), RECORDER)
    Path(RECORDER).chmod(0o755)
    hosts = Path('/etc/hosts')
    if 'sudo-it' not in hosts.read_text():
        with hosts.open('a') as stream:
            stream.write('\n127.0.1.1 sudo-it\n')
    Path('/usr/bin/sudoedit').unlink(missing_ok=True)
    Path('/usr/bin/sudoedit').symlink_to('sudo')
    put('/etc/sudo.conf', '', 0o644)
    for name in ('sudo', 'visudo'):
        os.chown('/opt/impl/' + name, 0, 0)
    for name in ('sudo', 'sudo-i'):
        pam = Path('/etc/pam.d') / name
        if pam.exists():
            source = pam.read_text()
            source = source.replace('@include common-auth',
                                    'auth required pam_unix.so nodelay')
            pam.write_text(source)
    BASELINE.update(snapshot())


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--seed', type=int, default=2119172)
    parser.add_argument('--sudo-cases', type=int, default=3000)
    parser.add_argument('--visudo-cases', type=int, default=3000)
    parser.add_argument('--budget', type=float, default=6000)
    parser.add_argument('--timeout', type=float, default=5)
    parser.add_argument('--shrink-budget', type=int, default=24)
    parser.add_argument('--replay')
    args = parser.parse_args()
    setup()
    logger = Logger()
    started = time.monotonic()
    counts = collections.Counter()
    classes = {}
    deviations = collections.Counter()
    pending = []
    output = OUT / ('seed-' + str(args.seed))
    output.mkdir(parents=True, exist_ok=True)
    failures = (output / 'findings.jsonl').open('w')
    print(f'conformance seed={args.seed} sudo={args.sudo_cases} '
          f'visudo={args.visudo_cases} budget={args.budget:g}s', flush=True)
    try:
        if args.replay:
            scenario = json.loads(Path(args.replay).read_text())['scenario']
            raw, normal = compare(scenario, logger, args.timeout)
            save_case(output / 'replay', scenario, raw, normal, 'replay')
            print(json.dumps(normal, indent=2))
            status, key = judge(scenario, raw, normal, logger, args.timeout)
            print(status, key or '')
            return int(status == 'different')
        exhausted = False
        for mode, count in [('sudo', args.sudo_cases), ('visudo', args.visudo_cases)]:
            for scenario in generate(args.seed, count, mode, Path(RECORDER).read_bytes()):
                if time.monotonic() - started >= args.budget:
                    exhausted = True
                    break
                raw, normal = compare(scenario, logger, args.timeout)
                counts[mode] += 1
                status, key = judge(scenario, raw, normal, logger, args.timeout)
                if status == 'equal':
                    counts['equal'] += 1
                    continue
                if status == 'deviation':
                    deviations[key] += 1
                    if deviations[key] == 1:
                        save_case(output / ('deviation-' + key), scenario, raw, normal,
                                  'documented deviation: ' + key)
                    continue
                counts['different'] += 1
                failures.write(json.dumps(dict(scenario=scenario, classes=key,
                                               raw=raw), ensure_ascii=True) + '\n')
                failures.flush()
                for name in key:
                    if name not in classes:
                        ident = hashlib.sha256(name.encode()).hexdigest()[:12]
                        classes[name] = dict(id=ident, count=0, feature=scenario['feature'])
                        pending.append((name, ident, scenario))
                        save_case(output / ident, scenario, raw, normal, 'unshrunk: ' + name)
                    classes[name]['count'] += 1
            if exhausted:
                break
        for name, ident, scenario in pending:
            if time.monotonic() - started >= args.budget:
                counts['unshrunk'] += 1
                continue
            reduced, raw, normal, attempts = shrink(
                scenario, name, logger, args.timeout, args.shrink_budget)
            save_case(output / ident, reduced, raw, normal, name, attempts)
            counts['shrunk'] += 1
        summary = dict(seed=args.seed, counts=dict(counts), deviations=dict(deviations),
                       classes=classes, exhausted=exhausted,
                       elapsed_seconds=round(time.monotonic() - started, 3))
        put(output / 'summary.json', json.dumps(summary, indent=2) + '\n', 0o644)
        line = (f"SUMMARY seed={args.seed} sudo={counts['sudo']} visudo={counts['visudo']} "
                f"equal={counts['equal']} deviations={sum(deviations.values())} "
                f"differences={counts['different']} classes={len(classes)} "
                f"shrunk={counts['shrunk']} unshrunk={counts['unshrunk']} "
                f"budget_exhausted={str(exhausted).lower()}")
        print(line, flush=True)
        put(output / 'summary.txt', line + '\n', 0o644)
        return int(bool(counts['different'] or exhausted or counts['unshrunk']))
    finally:
        failures.close()
        logger.close()
        uid = int(os.environ.get('HOST_UID', '0'))
        gid = int(os.environ.get('HOST_GID', '0'))
        for path in OUT.rglob('*'):
            os.chown(path, uid, gid)


if __name__ == '__main__':
    sys.exit(main())
