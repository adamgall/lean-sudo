#!/usr/bin/python3
import json
import os
import resource
import signal
import sys
import time


fds = {}
for entry in os.listdir('/proc/self/fd'):
    try:
        target = os.readlink('/proc/self/fd/' + entry)
        with open('/proc/self/fdinfo/' + entry) as stream:
            flags = next(line.split(':', 1)[1].strip() for line in stream
                         if line.startswith('flags:'))
        fds[entry] = {'target': target, 'flags': flags}
    except (FileNotFoundError, StopIteration):
        pass
mask = signal.pthread_sigmask(signal.SIG_BLOCK, [])
limits = {name: resource.getrlimit(getattr(resource, name))
          for name in dir(resource) if name.startswith('RLIMIT_')}
umask = os.umask(0)
os.umask(umask)
try:
    cwd = os.getcwd()
except OSError as error:
    cwd = '<' + os.strerror(error.errno) + '>'
with open('/proc/self/environ', 'rb') as stream:
    environ = [entry.decode('utf-8', 'surrogateescape')
               for entry in stream.read().split(b'\0') if entry]
result = dict(uid=os.getresuid(), gid=os.getresgid(), groups=os.getgroups(),
              cwd=cwd, umask=oct(umask), environment=dict(os.environ), environ=environ,
              descriptors=fds, limits=limits, signal_mask=sorted(map(int, mask)),
              argv=sys.argv)
with open('/var/lib/conformance/record.json', 'w') as stream:
    json.dump(result, stream, sort_keys=True)
print('conformance recorder ran', flush=True)
if sys.argv[1:2] == ['--sleep']:
    time.sleep(float(sys.argv[2]))
