# Real sudo.ws 1.9.17p2 timestamp interoperability on Ubuntu's little-endian
# 64-bit ABI. Run ^timestamp-interop- against the reference runner first: there
# /usr/bin/sudo and /usr/bin/sudo.ws are both the installed reference program.
# Source: sudo-project/sudo v1.9.17p2 plugins/sudoers/{timestamp.c,timestamp.h}.
# Every sudo child has argv[0]="sudo" and the SAME real UID. In particular, do
# not pipe a password into a shell function: that would change sudo's parent.
# Review regressions below exercise timestamp.c ts_find_record/ts_match_record,
# timestamp_status and timestamp_remove, plus check.c MODE_IGNORE_TICKET.
# Slot identity deliberately precedes validity: GLOBAL ignores start_time when
# matching, but timestamp_status validates BOTH timespecs even for GLOBAL.

timestamp_interop_setup() {
  local scope=$1 timeout=${2:-5} owner=${3:-root} directory=${4:-custom}
  TI_ROOT=$(mktemp -d /run/timestamp-interop.XXXXXX)
  chmod 0755 "$TI_ROOT"
  TI_STORE=$TI_ROOT/ts
  [[ $directory == default ]] && TI_STORE=/run/sudo/ts
  TI_UID=$(uid_of alice)
  TI_OWNER=$owner
  TI_SCOPE=$scope
  install -d -o alice -g "$(gid_of alice)" -m 0700 "$TI_ROOT/client"
  install -m 0440 /dev/stdin /etc/sudoers.d/zz-timestamp-interop <<EOF
Defaults:alice authenticate,!rootpw,!targetpw,!runaspw,lecture=never,passwd_tries=1,verifypw=always,timestamp_type=$scope,timestamp_timeout=$timeout,timestampowner=$owner
alice ALL=(root) PASSWD: /usr/bin/id, /usr/bin/true
EOF
  if [[ $directory != default ]]; then
    printf 'Defaults:alice timestampdir=%s\n' "$TI_STORE" >>/etc/sudoers.d/zz-timestamp-interop
  fi
  cat >"$TI_ROOT/client.sh" <<'SH'
#!/bin/bash
set -eu
root=$1 action=$2 writer=$3 reader=$4 scope=$5
out=$root/client/out err=$root/client/err
bad() {
  printf 'timestamp-interop: %s\n' "$*" >&2
  cat "$out" "$err" >&2
  exit 1
}
call() {
  local binary=$1 expected=$2 status=0
  shift 2
  /bin/bash -c 'exec -a sudo "$@"' sh "$binary" "$@" >"$out" 2>"$err" || status=$?
  [[ $status == "$expected" ]] || bad "$binary $*: expected $expected, got $status"
}
denied() {
  call "$1" 1 -n /usr/bin/id -u
  [[ ! -s $out ]] || bad 'unauthenticated command produced output'
  grep -qF 'a password is required' "$err" || bad 'denial was not authentication-required'
}
authenticate() {
  call "$1" 0 -S -p 'timestamp-interop-password: ' -v <<<'alicepw'
  grep -qF 'timestamp-interop-password: ' "$err" || bad 'validation did not actually prompt'
  [[ ! -s $out ]] || bad 'validation produced command output'
}
cached() {
  call "$1" 0 -n /usr/bin/id -u
  [[ $(cat "$out") == 0 ]] || bad 'cached command did not execute as root'
  [[ ! -s $err ]] || bad 'cached command emitted diagnostics'
}
fresh() {
  denied "$writer"
  denied "$reader"
  call "$writer" 1 -S -p 'timestamp-interop-password: ' -v <<<'timestamp-interop-wrong-password'
  grep -qF '1 incorrect password attempt' "$err" || bad 'wrong password was not rejected'
  authenticate "$writer"
}
metadata() {
  python3 "$root/records.py" metadata "$root/client/meta.json" "$scope" "$1"
}
case $action in
  cross)
    metadata before
    fresh
    cached "$reader"
    cached "$writer"
    metadata after
    ;;
  scopes)
    fresh
    cached "$reader"
    # A separate bash, kept alive by its post-command marker, is a distinct
    # parent in the same controlling tty/session (not a final-command exec).
    child_action=probe-denied
    [[ $scope == tty || $scope == global ]] && child_action=probe-cached
    /bin/bash "$root/client.sh" "$root" "$child_action" "$writer" "$reader" "$scope"
    cached "$reader"
    ;;
  invalidate-k)
    metadata before
    fresh
    cached "$reader"
    call "$reader" 0 -k
    denied "$writer"
    denied "$reader"
    metadata after
    ;;
  invalidate-K)
    fresh
    cached "$reader"
    call "$reader" 0 -K
    # Stop before any further sudo can recreate the file. Root checks unlink.
    ;;
  timeout-zero)
    fresh
    denied "$reader"
    denied "$writer"
    ;;
  timeout-short)
    fresh
    cached "$reader"
    # 0.05 minutes = 3 seconds; a 4-second wait crosses the real clock expiry.
    sleep 4
    denied "$reader"
    denied "$writer"
    authenticate "$reader"
    cached "$writer"
    ;;
  lock-refresh|lock-interrupt|lock-interrupt-ignored)
    metadata before
    denied "$writer"
    denied "$reader"
    # The reference authenticates the actual slot. The selected writer then
    # authenticates and refreshes it again; no success ticket is invented.
    authenticate /usr/bin/sudo.ws
    call "$writer" 0 -k
    authenticate "$writer"
    printf 'timestamp-interop-lock-ready:%s\n' "$$"
    IFS= read -r gate
    [[ $gate == start ]] || bad 'invalid root lock gate'
    if [[ $action == lock-refresh ]]; then
      cached "$reader"
    else
      # Normalize the child's disposition explicitly: a background harness may
      # have passed SIG_IGN through Bash. Python exec preserves this PID/PPID.
      disposition=default status=0
      if [[ $action == lock-interrupt-ignored ]]; then
        disposition=ignored
      fi
      /usr/bin/python3 "$root/records.py" exec-reader "$disposition" "$reader" \
        -n /usr/bin/id -u >"$out" 2>"$err" || status=$?
      # Both dispositions yield authentication-required in sudo.ws 1.9.17p2:
      # the frontend installs its own handler before timestamp locking.
      [[ $status == 1 ]] || bad "interrupted $reader: expected 1, got $status"
      [[ ! -s $out ]] || bad 'interrupted waiter executed the command'
      grep -qF 'a password is required' "$err" || bad 'interrupted lock did not fall back to authentication-required'
    fi
    ;;
  review-*)
    metadata before
    [[ $action == review-ignore-missing ]] || authenticate /usr/bin/sudo.ws
    printf 'timestamp-interop-review-ready:%s\n' "$$"
    IFS= read -r gate
    [[ $gate == start ]] || bad 'invalid root review gate'
    case $action in
      review-negative-sid-followed-valid|review-nonglobal-invalid-start|review-many-records|review-sparse-records)
        cached "$reader"
        ;;
      review-negative-sid-first-duplicate|review-invalid-time-first-duplicate|review-global-invalid-start)
        denied "$reader"
        ;;
      review-negative-sid-k|review-malformed-known-k)
        call "$reader" 0 -k
        [[ ! -s $out && ! -s $err ]] || bad '-k emitted unexpected output'
        ;;
      review-ignore-missing|review-ignore-existing)
        # Even an existing CURRENT ticket must not satisfy -k command.
        call "$reader" 1 -k -n /usr/bin/id -u
        [[ ! -s $out ]] || bad '-k -n ran without authentication'
        grep -qF 'a password is required' "$err" || bad '-k -n denial was not authentication-required'
        call "$reader" 0 -k -S -p 'timestamp-interop-password: ' /usr/bin/id -u <<<'alicepw'
        [[ $(cat "$out") == 0 ]] || bad '-k authenticated command did not run as root'
        grep -qF 'timestamp-interop-password: ' "$err" || bad '-k command did not prompt'
        ;;
      *) bad "unknown review action $action" ;;
    esac
    ;;
  probe-denied) denied "$reader" ;;
  probe-cached) cached "$reader" ;;
  *) bad "unknown client action $action" ;;
esac
printf 'timestamp-interop-ok:%s\n' "$action"
SH
  cat >"$TI_ROOT/records.py" <<'PY'
import json
import os
from pathlib import Path
import pwd
import stat
import struct
import sys
import time

# timestamp_entry: four u16s, uid_t, pid_t, two signed 64-bit timespecs,
# then an eight-byte dev_t/pid_t union. Explicit little endian, no host ABI.
ENTRY = struct.Struct('<HHHHIiqqqqQ')
LOCK = ENTRY.pack(2, 56, 4, 0, 0, 0, 0, 0, 0, 0, 0)
assert ENTRY.size == 56

def start_ns(pid):
    fields = Path(f'/proc/{pid}/stat').read_text().rsplit(')', 1)[1].split()
    return int(fields[19]) * 1_000_000_000 // os.sysconf('SC_CLK_TCK')

def entries(data):
    assert len(data) % ENTRY.size == 0, ('partial record', len(data))
    rows = list(ENTRY.iter_unpack(data))
    assert rows and data[:56] == LOCK, ('missing v2 LOCKEXCL', data[:56].hex())
    for row in rows:
        assert row[0:2] == (2, 56), row
        assert row[2] in (1, 2, 3, 4) and row[3] in (0, 1), row
        assert row[6] >= 0 and 0 <= row[7] < 1_000_000_000, row
        assert row[8] >= 0 and 0 <= row[9] < 1_000_000_000, row
    return rows

action, *args = sys.argv[1:]
if action == 'metadata':
    path, scope, phase = args
    path = Path(path)
    now = time.clock_gettime_ns(time.CLOCK_BOOTTIME)
    if phase == 'before':
        parent = os.getppid()
        sid = os.getsid(0)
        data = dict(ppid=parent, sid=sid, start=start_ns(sid if scope == 'tty' else parent),
                    ttydev=os.stat(f'/proc/{parent}/fd/0').st_rdev, before=now)
    else:
        data = json.loads(path.read_text())
        data['after'] = now
    path.write_text(json.dumps(data))
elif action in ('layout', 'disabled'):
    directory, uid, owner, scope, metadata = args
    uid = int(uid)
    directory = Path(directory)
    user = pwd.getpwnam(owner)
    ds = directory.stat()
    assert stat.S_ISDIR(ds.st_mode) and stat.S_IMODE(ds.st_mode) == 0o700, ds
    assert (ds.st_uid, ds.st_gid) == (user.pw_uid, user.pw_gid), ds
    # sudo.ws uses the decimal invoking UID, NOT the login name or auth UID.
    assert sorted(p.name for p in directory.iterdir()) == [str(uid)], list(directory.iterdir())
    path = directory / str(uid)
    fs = path.stat()
    assert stat.S_ISREG(fs.st_mode) and stat.S_IMODE(fs.st_mode) == 0o600, fs
    assert fs.st_uid == user.pw_uid and fs.st_nlink == 1, fs
    rows = entries(path.read_bytes())
    meta = json.loads(Path(metadata).read_text())
    kind = dict(global_=1, tty=2, ppid=3)[scope if scope != 'global' else 'global_']
    selected = [r for r in rows if r[2] == kind and r[4] == uid]
    assert len(selected) == 1, rows
    row = selected[0]
    assert row[5] == meta['sid'], (row, meta)
    if scope != 'global':
        assert row[10] == meta['ttydev' if scope == 'tty' else 'ppid'], (row, meta)
        assert row[6] * 1_000_000_000 + row[7] == meta['start'], (row, meta)
    if action == 'disabled':
        assert row[3] & 1, row
    else:
        assert row[3] == 0, row
        stamp = row[8] * 1_000_000_000 + row[9]
        assert meta['before'] <= stamp <= meta['after'], (stamp, meta)
    # Global caching still has its separate per-parent serialization slot.
    assert len(rows) == (3 if scope == 'global' else 2), rows
    if scope == 'global':
        locks = [r for r in rows if r[2] == 3]
        assert len(locks) == 1 and locks[0][3] == 1, rows
        assert locks[0][10] == meta['ppid'], (locks, meta)
    print('timestamp-interop-v2-layout-ok')
elif action == 'mutate':
    source, dest, variant = args
    data = Path(source).read_bytes()
    rows = entries(data)
    offset = next(i * 56 for i, row in enumerate(rows) if row[2] == 1)
    row = list(ENTRY.unpack_from(data, offset))
    assert row[3] == 0, row
    if variant == 'foreign-auth-uid':
        row[4] = pwd.getpwnam('bob').pw_uid
    elif variant == 'unsupported-version':
        row[0] = 3
    elif variant == 'unsupported-type':
        row[2] = 99
    elif variant == 'disabled':
        row[3] = 1
    elif variant == 'negative-seconds':
        row[8] = -1
    elif variant == 'invalid-nanoseconds':
        row[9] = 1_000_000_000
    elif variant == 'future':
        row[8] = time.clock_gettime_ns(time.CLOCK_BOOTTIME) // 1_000_000_000 + 3600
    elif variant == 'zero-size':
        row[1] = 0
    elif variant == 'unsupported-size':
        row[1] = 64
    elif variant not in ('truncated', 'corrupt-header', 'skip-foreign'):
        raise AssertionError(variant)
    changed = ENTRY.pack(*row)
    if variant == 'unsupported-size':
        changed += b'foreign!'
    data = data[:offset] + changed + data[offset + 56:]
    if variant == 'truncated':
        data = data[:offset + 31]
    elif variant == 'corrupt-header':
        data = b'not-a-sudo-timestamp\x00'
    elif variant == 'skip-foreign':
        # Keep the valid global ticket AFTER three unsupported records. Their
        # declared sizes must be honored and their bytes/offsets preserved.
        foreign_version = list(row)
        foreign_version[0] = 3
        foreign_type = list(row)
        foreign_type[2] = 99
        foreign_size = list(row)
        foreign_size[1] = 72
        sentinels = (ENTRY.pack(*foreign_version) + ENTRY.pack(*foreign_type) +
                     ENTRY.pack(*foreign_size) + b'opaque-extension')
        assert len(sentinels) == 184
        data = data[:offset] + sentinels + data[offset:]
        Path(dest + '.sentinel').write_bytes(sentinels)
        Path(dest + '.offset').write_text(str(offset))
    # Keep the real file's ownership/mode; this is deliberate disk corruption,
    # not a substitute authentication service or a synthetic success ticket.
    Path(dest).write_bytes(data)
elif action == 'preserved':
    path, = args
    data = Path(path).read_bytes()
    offset = int(Path(path + '.offset').read_text())
    sentinels = Path(path + '.sentinel').read_bytes()
    assert data[offset:offset + len(sentinels)] == sentinels, data.hex()
    row = ENTRY.unpack_from(data, offset + len(sentinels))
    assert row[:4] == (2, 56, 1, 0), row
    print('timestamp-interop-foreign-records-preserved')
elif action == 'exec-reader':
    import signal

    disposition, binary, *argv = args
    assert disposition in ('default', 'ignored'), disposition
    handler = signal.SIG_DFL if disposition == 'default' else signal.SIG_IGN
    signal.signal(signal.SIGINT, handler)
    signal.signal(signal.SIGQUIT, handler)
    os.execv(binary, ['sudo', *argv])
elif action == 'locking':
    import fcntl
    import select
    import signal
    import subprocess

    root, directory, uid, writer, reader, mode = args
    user = pwd.getpwnam('alice')
    env = dict(HOME=user.pw_dir, USER=user.pw_name, LOGNAME=user.pw_name,
               SHELL='/bin/bash', PATH='/usr/bin:/bin', LANG='C.UTF-8')
    # exec through setpriv retains one stable bash parent for ALL sudo calls.
    # A private session also lets failure cleanup kill every descendant.
    child = subprocess.Popen(
        ['setpriv', '--reuid=alice', f'--regid={user.pw_gid}', '--init-groups',
         '--', '/bin/bash', root + '/client.sh', root, 'lock-' + mode,
         writer, reader, 'ppid'],
        cwd=user.pw_dir, env=env, start_new_session=True,
        stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
        text=True)
    fd = None
    ready = output = errors = ''
    try:
        assert select.select([child.stdout], [], [], 15)[0], 'authentication gate timed out'
        ready = child.stdout.readline()
        assert ready == f'timestamp-interop-lock-ready:{child.pid}\n', ready
        path = Path(directory) / uid
        fd = os.open(path, os.O_RDWR)
        data = os.pread(fd, os.fstat(fd).st_size, 0)
        rows = entries(data)
        selected = [(i * 56, row) for i, row in enumerate(rows)
                    if row[2] == 3 and row[4] == int(uid) and row[10] == child.pid]
        assert len(selected) == 1, rows
        offset, row = selected[0]
        assert row[3] == 0, row
        authenticated = data[offset:offset + 56]
        fcntl.lockf(fd, fcntl.LOCK_EX, 56, offset, os.SEEK_SET)
        # While holding ONLY the selected record, make it unusable. Restore
        # these real authenticated bytes before releasing: the waiter must
        # read after obtaining the lock, not consume a pre-lock stale snapshot.
        disabled = list(row)
        disabled[3] |= 1
        assert os.pwrite(fd, ENTRY.pack(*disabled), offset) == 56
        child.stdin.write('start\n')
        child.stdin.flush()
        info = os.fstat(fd)
        identity = (os.major(info.st_dev), os.minor(info.st_dev), info.st_ino)
        deadline = time.monotonic() + 8
        waiter = None
        while time.monotonic() < deadline:
            assert child.poll() is None, 'reader finished without waiting for the selected record'
            for line in Path('/proc/locks').read_text().splitlines():
                fields = line.split()
                if len(fields) != 9 or fields[1:5] != ['->', 'POSIX', 'ADVISORY', 'WRITE']:
                    continue
                major, minor, inode = fields[6].split(':')
                if (int(major, 16), int(minor, 16), int(inode)) != identity:
                    continue
                if fields[7:] != [str(offset), str(offset + 55)]:
                    continue
                pid = int(fields[5])
                proc = Path(f'/proc/{pid}/stat').read_text().rsplit(')', 1)[1].split()
                assert int(proc[1]) == child.pid, ('unexpected lock waiter parent', line, proc)
                waiter = pid
                break
            if waiter is not None:
                break
            time.sleep(0.01)
        assert waiter is not None, 'no POSIX waiter on the selected 56-byte record'
        if mode == 'refresh':
            assert os.pwrite(fd, authenticated, offset) == 56
            fcntl.lockf(fd, fcntl.LOCK_UN, 56, offset, os.SEEK_SET)
        else:
            assert mode in ('interrupt', 'interrupt-ignored'), mode
            os.kill(waiter, signal.SIGINT)
        # Both interruption cases must finish while the record stays locked:
        # sudo.ws falls back to authentication for both initial dispositions.
        output, errors = child.communicate(timeout=8)
        assert child.returncode == 0, (child.returncode, output, errors)
        assert f'timestamp-interop-ok:lock-{mode}\n' in output, output
        print(f'timestamp-interop-posix-lock-{mode}-ok')
    finally:
        if child.poll() is None:
            os.killpg(child.pid, signal.SIGKILL)
        if child.stdout is not None and not child.stdout.closed:
            output, errors = child.communicate()
        if fd is not None:
            os.close(fd)
        sys.stdout.write(ready + output)
        sys.stderr.write(errors)
elif action == 'review':
    import ctypes
    import fcntl
    import select
    import signal
    import subprocess

    root, directory, uid, binary, scope, variant = args
    user = pwd.getpwnam('alice')
    env = dict(HOME=user.pw_dir, USER=user.pw_name, LOGNAME=user.pw_name,
               SHELL='/bin/bash', PATH='/usr/bin:/bin', LANG='C.UTF-8')
    child = subprocess.Popen(
        ['setpriv', '--reuid=alice', f'--regid={user.pw_gid}', '--init-groups',
         '--', '/bin/bash', root + '/client.sh', root, 'review-' + variant,
         '/usr/bin/sudo.ws', binary, scope],
        cwd=user.pw_dir, env=env, start_new_session=True,
        stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
        text=True)
    fd = watch = None
    ready = output = errors = ''
    try:
        assert select.select([child.stdout], [], [], 15)[0], 'review authentication gate timed out'
        ready = child.stdout.readline()
        assert ready == f'timestamp-interop-review-ready:{child.pid}\n', ready
        path = Path(directory) / uid
        expected = None
        selected_offset = None
        many = variant in ('many-records', 'sparse-records')
        if variant == 'ignore-missing':
            assert not Path(directory).exists(), 'fixture unexpectedly created timestamp directory'
        else:
            original = path.read_bytes()
            rows = entries(original)
            kind = 1 if scope == 'global' else 3
            selected = [(i * 56, list(row)) for i, row in enumerate(rows)
                        if row[2] == kind and row[4] == int(uid)]
            assert len(selected) == 1, rows
            offset, valid = selected[0]
            assert valid[3] == 0, valid
            if scope == 'ppid':
                assert valid[10] == child.pid, (valid, child.pid)
            prefix, ticket, suffix = original[:offset], original[offset:offset + 56], original[offset + 56:]
            bad = valid.copy()
            disable = []
            if variant.startswith('negative-sid'):
                bad[5] = -1  # sudo.ws stores getsid()'s signed failure value.
                if variant == 'negative-sid-followed-valid':
                    bad[4] = pwd.getpwnam('bob').pw_uid
                fixture = prefix + ENTRY.pack(*bad) + ticket + suffix
                if variant == 'negative-sid-k':
                    disable = [offset, offset + 56]
                elif variant == 'negative-sid-followed-valid':
                    selected_offset = offset + 56
            elif variant == 'invalid-time-first-duplicate':
                bad[9] = 1_000_000_000
                fixture = prefix + ENTRY.pack(*bad) + ticket + suffix
            elif variant in ('global-invalid-start', 'nonglobal-invalid-start'):
                bad[7] = 1_000_000_000
                fixture = prefix + ENTRY.pack(*bad) + ticket + suffix
                if variant == 'nonglobal-invalid-start':
                    selected_offset = offset + 56
            elif variant == 'malformed-known-k':
                # SID/time are NOT part of identity. -k must disable every
                # matching UID (TS_ANYUID is on the search key), preserving
                # the malformed bytes. Unsupported formats are skipped.
                damaged = []
                for field, value in ((5, -1), (8, -1), (9, 1_000_000_000)):
                    row = valid.copy()
                    row[field] = value
                    row[4] = pwd.getpwnam('bob').pw_uid
                    disable.append(offset + len(damaged) * 56)
                    damaged.append(ENTRY.pack(*row))
                for field, value in ((0, 3), (2, 99), (7, 1_000_000_000)):
                    row = valid.copy()
                    row[field] = value
                    damaged.append(ENTRY.pack(*row))
                disable.append(offset + len(damaged) * 56)
                fixture = prefix + b''.join(damaged) + ticket + suffix
            elif many:
                # These are fixture sizes, not format/implementation caps.
                # Dense records exceed the former 64 KiB cutoff; sparse
                # extension records force declared-size seeks over 256 MiB.
                count = 32768 if variant == 'many-records' else 4096
                stride = 56 if variant == 'many-records' else 65535
                foreign = valid.copy()
                foreign[4] = pwd.getpwnam('bob').pw_uid
                foreign[1] = stride
                if variant == 'sparse-records':
                    foreign[0] = 3
                sentinel = ENTRY.pack(*foreign)
                with path.open('r+b') as stream:
                    stream.truncate(0)
                    stream.write(prefix)
                    for index in range(count):
                        stream.seek(offset + index * stride)
                        stream.write(sentinel)
                    selected_offset = offset + count * stride
                    stream.seek(selected_offset)
                    stream.write(ticket + suffix)
                expected_size = selected_offset + len(ticket) + len(suffix)
            else:
                assert variant == 'ignore-existing', variant
                fixture = original
            if not many:
                path.write_bytes(fixture)
                expected = bytearray(fixture)
                for position in disable:
                    flags, = struct.unpack_from('<H', expected, position + 6)
                    struct.pack_into('<H', expected, position + 6, flags | 1)
            if variant == 'ignore-existing':
                fd = os.open(path, os.O_RDWR)
                fcntl.lockf(fd, fcntl.LOCK_EX, 56, 0, os.SEEK_SET)
        if variant in ('ignore-existing', 'ignore-missing'):
            # inotify complements the held LOCKEXCL: an implementation that
            # merely opens without locking must fail too. Register AFTER our
            # own opens; inspect events BEFORE our post-command file reads.
            libc = ctypes.CDLL(None, use_errno=True)
            watch = libc.inotify_init1(os.O_NONBLOCK | os.O_CLOEXEC)
            assert watch >= 0, ('inotify_init1', ctypes.get_errno())
            watched = path if variant == 'ignore-existing' else Path(root)
            # IN_OPEN | IN_MODIFY | IN_ATTRIB | IN_CREATE | IN_DELETE |
            # IN_MOVED_FROM | IN_MOVED_TO | IN_DELETE_SELF | IN_MOVE_SELF
            mask = 0x20 | 0x2 | 0x4 | 0x100 | 0x200 | 0x40 | 0x80 | 0x400 | 0x800
            assert libc.inotify_add_watch(watch, os.fsencode(watched), mask) >= 0, (
                'inotify_add_watch', ctypes.get_errno())
        child.stdin.write('start\n')
        child.stdin.flush()
        output, errors = child.communicate(timeout=30 if many else 10)
        assert child.returncode == 0, (child.returncode, output, errors)
        assert f'timestamp-interop-ok:review-{variant}\n' in output, output
        if watch is not None:
            assert not select.select([watch], [], [], 0)[0], '-k command opened/changed timestamp storage'
        if variant == 'ignore-missing':
            assert not Path(directory).exists(), '-k command created timestamp storage'
        elif many:
            assert path.stat().st_size == expected_size, 'scan appended or truncated a slot'
            # Keep fixture verification bounded too; never read sparse holes.
            with path.open('rb') as stream:
                assert stream.read(len(prefix)) == prefix
                for index in range(count):
                    stream.seek(offset + index * stride)
                    assert stream.read(56) == sentinel, ('foreign record changed', index)
                stream.seek(selected_offset)
                refreshed = stream.read(56)
                assert refreshed[:32] == ticket[:32] and refreshed[48:] == ticket[48:], refreshed.hex()
                assert stream.read() == suffix
        else:
            actual = path.read_bytes()
            if selected_offset is not None:
                # Successful cached commands refresh only the chosen ticket's
                # timestamp. Earlier malformed/foreign slots must stay intact.
                stamp = slice(selected_offset + 32, selected_offset + 48)
                expected[stamp] = actual[stamp]
            assert actual == expected, ('unexpected slot append/rewrite', actual.hex(), expected.hex())
        print(f'timestamp-interop-review-{variant}-ok')
    finally:
        if child.poll() is None:
            os.killpg(child.pid, signal.SIGKILL)
        if child.stdout is not None and not child.stdout.closed:
            output, errors = child.communicate()
        if watch is not None:
            os.close(watch)
        if fd is not None:
            os.close(fd)
        sys.stdout.write(ready + output)
        sys.stderr.write(errors)
else:
    raise AssertionError(action)
PY
}

timestamp_interop_cleanup() {
  rm -rf "$TI_ROOT"
  rm -f /etc/sudoers.d/zz-timestamp-interop
}

timestamp_interop_client() {
  local action=$1 writer=$2 reader=$3 terminal=${4:-$TI_SCOPE}
  local snippet="exec /bin/bash '$TI_ROOT/client.sh' '$TI_ROOT' '$action' '$writer' '$reader' '$TI_SCOPE'"
  if [[ $terminal == tty ]]; then
    pty alice "$snippet"
  else
    run alice "$snippet"
  fi
  expect_rc 0
  expect_out_has "timestamp-interop-ok:$action"
}

timestamp_interop_layout() {
  python3 "$TI_ROOT/records.py" "${1:-layout}" "$TI_STORE" "$TI_UID" "$TI_OWNER" "$TI_SCOPE" "$TI_ROOT/client/meta.json" >>"$LOG" 2>&1 || fail 'timestamp v2 ABI, scope, clock or storage metadata mismatch (see log)'
}

for timestamp_interop_direction in reference-to-installed installed-to-reference; do
  timestamp_interop_writer=/usr/bin/sudo.ws
  timestamp_interop_reader=/usr/bin/sudo
  if [[ $timestamp_interop_direction == installed-to-reference ]]; then
    timestamp_interop_writer=/usr/bin/sudo
    timestamp_interop_reader=/usr/bin/sudo.ws
  fi
  for timestamp_interop_scope in ppid tty global; do
    begin "timestamp-interop-$timestamp_interop_direction-$timestamp_interop_scope-v2-layout" && {
      timestamp_interop_setup "$timestamp_interop_scope"
      timestamp_interop_client cross "$timestamp_interop_writer" "$timestamp_interop_reader"
      timestamp_interop_layout
      [[ ! -e /run/sudo/ts/$TI_UID ]] || fail 'timestampdir override leaked a default-directory ticket'
      timestamp_interop_cleanup
      end
    }

    begin "timestamp-interop-$timestamp_interop_direction-$timestamp_interop_scope-parent-session-isolation" && {
      timestamp_interop_setup "$timestamp_interop_scope"
      # Both ppid and tty cases run on a real pty, so only the parent changes
      # for the nested bash. A later pty invocation is a genuinely new session.
      timestamp_interop_client scopes "$timestamp_interop_writer" "$timestamp_interop_reader" tty
      timestamp_interop_probe=probe-denied
      [[ $timestamp_interop_scope == global ]] && timestamp_interop_probe=probe-cached
      timestamp_interop_client "$timestamp_interop_probe" "$timestamp_interop_writer" "$timestamp_interop_reader" tty
      timestamp_interop_cleanup
      end
    }

    for timestamp_interop_remove in k K; do
      begin "timestamp-interop-$timestamp_interop_direction-$timestamp_interop_scope-$timestamp_interop_remove" && {
        timestamp_interop_setup "$timestamp_interop_scope"
        timestamp_interop_client "invalidate-$timestamp_interop_remove" "$timestamp_interop_writer" "$timestamp_interop_reader"
        if [[ $timestamp_interop_remove == K ]]; then
          [[ ! -e $TI_STORE/$TI_UID ]] || fail '-K did not unlink the other implementation timestamp file'
          timestamp_interop_client probe-denied "$timestamp_interop_reader" "$timestamp_interop_writer"
        else
          timestamp_interop_layout disabled
        fi
        timestamp_interop_cleanup
        end
      }
    done
  done

  for timestamp_interop_lock in refresh interrupt interrupt-ignored; do
    begin "timestamp-interop-$timestamp_interop_direction-posix-lock-$timestamp_interop_lock" && {
      timestamp_interop_setup ppid
      run root "python3 '$TI_ROOT/records.py' locking '$TI_ROOT' '$TI_STORE' '$TI_UID' '$timestamp_interop_writer' '$timestamp_interop_reader' '$timestamp_interop_lock'"
      expect_rc 0
      expect_out_has "timestamp-interop-posix-lock-$timestamp_interop_lock-ok"
      timestamp_interop_cleanup
      end
    }
  done

  for timestamp_interop_timeout in zero short; do
    begin "timestamp-interop-$timestamp_interop_direction-timeout-$timestamp_interop_timeout" && {
      timestamp_interop_minutes=0
      [[ $timestamp_interop_timeout == short ]] && timestamp_interop_minutes=0.05
      timestamp_interop_setup ppid "$timestamp_interop_minutes"
      timestamp_interop_client "timeout-$timestamp_interop_timeout" "$timestamp_interop_writer" "$timestamp_interop_reader"
      timestamp_interop_cleanup
      end
    }
  done

  begin "timestamp-interop-$timestamp_interop_direction-timestampowner" && {
    timestamp_interop_setup ppid 5 bob
    timestamp_interop_client cross "$timestamp_interop_writer" "$timestamp_interop_reader"
    timestamp_interop_layout
    timestamp_interop_cleanup
    end
  }

  begin "timestamp-interop-$timestamp_interop_direction-default-directory" && {
    timestamp_interop_setup ppid 5 root default
    timestamp_interop_client cross "$timestamp_interop_writer" "$timestamp_interop_reader"
    timestamp_interop_layout
    rm -f "$TI_STORE/$TI_UID"
    timestamp_interop_cleanup
    end
  }
done

# Build every damaged/foreign fixture from a ticket actually authenticated by
# sudo.ws. Restore identical bytes before each implementation, preventing the
# reference's defensive repair from hiding a reader bug in the installed sudo.
for timestamp_interop_variant in foreign-auth-uid unsupported-version unsupported-type unsupported-size disabled negative-seconds invalid-nanoseconds future zero-size truncated corrupt-header skip-foreign; do
  begin "timestamp-interop-record-$timestamp_interop_variant" && {
    timestamp_interop_setup global
    timestamp_interop_client cross /usr/bin/sudo.ws /usr/bin/sudo.ws
    timestamp_interop_layout
    cp -p "$TI_STORE/$TI_UID" "$TI_ROOT/reference-ticket"
    for timestamp_interop_binary in /usr/bin/sudo.ws /usr/bin/sudo; do
      python3 "$TI_ROOT/records.py" mutate "$TI_ROOT/reference-ticket" "$TI_STORE/$TI_UID" "$timestamp_interop_variant" >>"$LOG" 2>&1 || fail 'could not construct reference-backed damaged timestamp fixture'
      timestamp_interop_probe=probe-denied
      [[ $timestamp_interop_variant == skip-foreign ]] && timestamp_interop_probe=probe-cached
      timestamp_interop_client "$timestamp_interop_probe" "$timestamp_interop_binary" "$timestamp_interop_binary"
      if [[ $timestamp_interop_variant == skip-foreign ]]; then
        python3 "$TI_ROOT/records.py" preserved "$TI_STORE/$TI_UID" >>"$LOG" 2>&1 || fail 'foreign records or the following valid ticket were overwritten/reordered'
      fi
    done
    timestamp_interop_cleanup
    end
  }
done

# Each case is independently filterable, starts with a real sudo.ws ticket,
# and uses one stable parent while root mutates that parent's private file.
# Do not use /run/sudo/ts here: cleanup must never touch a host user's ticket.
for timestamp_interop_review in negative-sid-followed-valid negative-sid-first-duplicate negative-sid-k malformed-known-k invalid-time-first-duplicate global-invalid-start nonglobal-invalid-start ignore-missing ignore-existing many-records sparse-records; do
  begin "timestamp-interop-review-$timestamp_interop_review" && {
    timestamp_interop_scope=ppid
    [[ $timestamp_interop_review == global-invalid-start ]] && timestamp_interop_scope=global
    for timestamp_interop_binary in /usr/bin/sudo.ws /usr/bin/sudo; do
      timestamp_interop_setup "$timestamp_interop_scope"
      run root "python3 '$TI_ROOT/records.py' review '$TI_ROOT' '$TI_STORE' '$TI_UID' '$timestamp_interop_binary' '$timestamp_interop_scope' '$timestamp_interop_review'"
      expect_rc 0
      expect_out_has "timestamp-interop-review-$timestamp_interop_review-ok"
      timestamp_interop_cleanup
    done
    end
  }
done
