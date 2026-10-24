#!/usr/bin/env python3
"""Run a shell snippet as USER inside a fresh pty session and script it.

usage: ptyrun.py [-t SECS] USER SNIPPET [-e REGEX -s TEXT | -e REGEX | -s TEXT]...

The child is a new session leader whose controlling terminal is the pty slave,
running `/bin/sh -c SNIPPET` with the user's uid/gid/supplementary groups and a
clean environment. Each `-e REGEX` waits (timeout -t, default 15s) until REGEX
matches output produced after the previous match; each `-s TEXT` writes TEXT to
the terminal (\\r and \\n escapes are interpreted) after a 0.1s "human" pause.

Prints the full transcript (CR stripped) to stdout. Exit status: the child's
exit status (128+N if killed by signal N), 124 if the session did not finish in
time, 125 if an expectation was not met (the transcript is still printed).
"""
import os
import pty
import pwd
import re
import select
import signal
import sys
import time


def main() -> int:
    args = sys.argv[1:]
    timeout = 15.0
    if args[:1] == ["-t"]:
        timeout = float(args[1])
        args = args[2:]
    if len(args) < 2:
        print(__doc__, file=sys.stderr)
        return 2
    user, snippet, steps = args[0], args[1], args[2:]
    script = []
    i = 0
    while i < len(steps):
        if steps[i] not in ("-e", "-s") or i + 1 >= len(steps):
            print(f"ptyrun: bad step {steps[i:]}", file=sys.stderr)
            return 2
        val = steps[i + 1]
        if steps[i] == "-s":
            val = val.replace("\\r", "\r").replace("\\n", "\n")
        script.append((steps[i], val))
        i += 2

    pw = pwd.getpwnam(user)
    env = {
        "HOME": pw.pw_dir,
        "USER": pw.pw_name,
        "LOGNAME": pw.pw_name,
        "SHELL": pw.pw_shell,
        "PATH": "/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin",
        "TERM": "dumb",
        "LANG": "C.UTF-8",
    }

    pid, fd = pty.fork()
    if pid == 0:  # child: session leader with the pty as controlling tty
        try:
            os.fchown(0, pw.pw_uid, -1)
            os.initgroups(pw.pw_name, pw.pw_gid)
            os.setgid(pw.pw_gid)
            os.setuid(pw.pw_uid)
            os.chdir(pw.pw_dir)
            os.execve("/bin/sh", ["sh", "-c", snippet], env)
        finally:
            os._exit(127)

    buf = bytearray()
    pos = 0  # expectations only match output after the previous match
    eof = False
    status = 0

    def pump(deadline: float) -> None:
        nonlocal eof
        while not eof:
            left = deadline - time.monotonic()
            if left <= 0:
                return
            r, _, _ = select.select([fd], [], [], left)
            if not r:
                return
            try:
                data = os.read(fd, 4096)
            except OSError:
                data = b""
            if not data:
                eof = True
                return
            buf.extend(data)
            return

    failed = None
    for kind, val in script:
        if kind == "-s":
            time.sleep(0.1)
            os.write(fd, val.encode())
            continue
        rx = re.compile(val.encode())
        deadline = time.monotonic() + timeout
        while True:
            m = rx.search(bytes(buf), pos)
            if m:
                pos = m.end()
                break
            if eof or time.monotonic() >= deadline:
                failed = f"expectation not met: /{val}/"
                break
            pump(deadline)
        if failed:
            break

    deadline = time.monotonic() + (1.0 if failed else timeout)
    while not eof and time.monotonic() < deadline:
        pump(deadline)
    timed_out = not eof
    if timed_out:
        os.kill(pid, signal.SIGKILL)
    _, wstatus = os.waitpid(pid, 0)
    os.close(fd)
    if os.WIFEXITED(wstatus):
        status = os.WEXITSTATUS(wstatus)
    else:
        status = 128 + os.WTERMSIG(wstatus)

    sys.stdout.write(buf.decode("utf-8", "replace").replace("\r", ""))
    sys.stdout.flush()
    if failed:
        print(f"ptyrun: {failed}", file=sys.stderr)
        return 125
    if timed_out:
        print("ptyrun: session timed out", file=sys.stderr)
        return 124
    return status


if __name__ == "__main__":
    sys.exit(main())
