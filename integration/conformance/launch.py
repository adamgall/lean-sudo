#!/usr/bin/python3
import ctypes
import json
import os
import pwd
import resource
import sys


def encode(value):
    return value.encode('utf-8', 'surrogateescape')


def strings(values):
    array = (ctypes.c_char_p * (len(values) + 1))()
    array[:-1] = [encode(value) for value in values]
    array[-1] = None
    return array


with open(sys.argv[1]) as stream:
    spec = json.load(stream)
user = pwd.getpwnam(spec['user'])
for name, pair in spec['limits'].items():
    resource.setrlimit(getattr(resource, name), tuple(pair))
directory = spec['cwd'] or user.pw_dir
if spec['cwd']:
    os.makedirs(directory, exist_ok=True)
    if os.getuid() == 0:
        os.chown(directory, user.pw_uid, user.pw_gid)
os.chdir(directory)
if os.getuid() == 0 and spec['drop']:
    os.initgroups(user.pw_name, user.pw_gid)
    os.setresgid(user.pw_gid, user.pw_gid, user.pw_gid)
    os.setresuid(user.pw_uid, user.pw_uid, user.pw_uid)
if spec['cwd_state'] == 'deleted':
    os.rmdir(directory)
elif spec['cwd_state'] == 'unreadable':
    os.chmod(directory, 0)
for item in spec['descriptors']:
    flags = os.O_RDWR if item['target'] == '/dev/null' else os.O_RDONLY
    opened = os.open(item['target'], flags)
    if opened != item['fd']:
        os.dup2(opened, item['fd'], inheritable=not item['cloexec'])
        os.close(opened)
    else:
        os.set_inheritable(opened, not item['cloexec'])
for fd in spec['close']:
    os.close(fd)
os.umask(int(spec['umask'], 8))
libc = ctypes.CDLL(None, use_errno=True)
libc.execve(encode(spec['argv'][0]), strings(spec['argv']), strings(spec['env']))
os.write(2, b'launch: execve failed\n')
os._exit(127)
