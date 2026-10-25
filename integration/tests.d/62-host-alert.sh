# Local-host DNS failures are raw parse alerts; remote -h failures use NO_LOG.
# Compare actual syslog datagrams and logfiles against installed sudo.ws.
host_alert_fixture() {
  cat >"$WORK/host-alert.py" <<'PY'
import json, os, re, socket, subprocess, sys, tempfile
binary, fmt, mode = sys.argv[1:]
policy = '/etc/sudoers.d/zz-host-alert'
logfile = '/tmp/host-alert.log'
saved_socket = None
nss = open('/etc/nsswitch.conf').read()
hosts = open('/etc/hosts').read()
hostname = socket.gethostname() if mode == 'local' else 'host-alert.invalid'
reason = 'unable to resolve host ' + hostname + ':'
sock = socket.socket(socket.AF_UNIX, socket.SOCK_DGRAM)
try:
    open('/etc/nsswitch.conf', 'w').write(re.sub(r'^hosts:.*$', 'hosts: files', nss, flags=re.M))
    if mode == 'local':
        open('/etc/hosts', 'w').write(''.join(line for line in hosts.splitlines(True)
                                           if hostname not in line.split()[1:]))
    open(policy, 'w').write('Defaults logfile="' + logfile + '", log_format=' + fmt + ', !log_allowed, !log_denied, !mail_always, syslog=authpriv, syslog_badpri=alert, !syslog_pid, loglinelen=0\nDefaults fqdn\nroot ALL=(ALL:ALL) NOPASSWD: ALL\n')
    os.chmod(policy, 0o440)
    if os.path.exists(logfile): os.unlink(logfile)
    if os.path.lexists('/dev/log'):
        fd, saved_socket = tempfile.mkstemp(prefix='host-alert-', dir='/dev')
        os.close(fd)
        os.replace('/dev/log', saved_socket)
    sock.bind('/dev/log')
    sock.settimeout(.1)
    options = [] if mode == 'local' else ['-h', hostname]
    p = subprocess.run(['/bin/bash', '-c', 'exec -a sudo "$@"', 'sh', binary,
                        '-n', *options, '-l'], stdin=subprocess.DEVNULL,
                       stdout=subprocess.PIPE, stderr=subprocess.PIPE, timeout=20)
    assert p.returncode == 0, (p.returncode, p.stdout, p.stderr)
    assert reason.encode() in p.stderr, p.stderr
    sys.stderr.buffer.write(p.stderr)
    events = []
    while True:
        try: message = sock.recv(65536).decode()
        except socket.timeout: break
        if reason not in message: continue
        match = re.search(r'^<([0-9]+)>.*?sudo(?:\[[0-9]+\])?: (.*)', message, re.S)
        assert match, message
        assert match[1] == '81', message
        body = match[2]
        events.append(body)
    assert bool(events) == (mode == 'local'), events
    print('syslog:', json.dumps(events, sort_keys=True))
    data = open(logfile).read() if os.path.exists(logfile) else ''
    # fqdn is an early Defaults callback, before logfile/log_format callbacks.
    assert not data, data
    print('logfile: none')
finally:
    sock.close()
    if os.path.lexists('/dev/log'): os.unlink('/dev/log')
    if saved_socket is not None: os.replace(saved_socket, '/dev/log')
    open('/etc/nsswitch.conf', 'w').write(nss)
    open('/etc/hosts', 'w').write(hosts)
    for path in (policy, logfile):
        if os.path.exists(path): os.unlink(path)
PY
}
for host_alert_mode in local remote; do
  for host_alert_format in sudo json_compact json_pretty; do
    begin "host-alert-$host_alert_mode-$host_alert_format" && {
      host_alert_fixture
      shell_policy_compare root "python3 '$WORK/host-alert.py' \"\$SP_BINARY\" '$host_alert_format' '$host_alert_mode'" 0
      rm -f "$WORK/host-alert.py"
      end
    }
  done
done
