cat >"$WORK/helper-mode.py" <<'PY'
import json
import os
import socket
import sys
import time

marker = "/etc/helper-marker"


def envelope(parent):
    plan = {"uid": 0, "gid": 0, "groups": [], "path": marker}
    data = {"magic": "lean-sudo-helper-1", "parent": parent, "effectiveUid": 0,
            "mask": 0, "name": "pam-admin", "payload": plan}
    return json.dumps(data).encode()


def channel(kind):
    if kind == "socket":
        left, right = socket.socketpair()
        return left.detach(), right.detach()
    return os.pipe()


def helper(plan_fd):
    os.dup2(plan_fd, 63, inheritable=True)
    os.execvp("sudo", ["sudo", "--lean-sudo-helper"])


def direct(kind):
    reader, writer = channel(kind)
    child = os.fork()
    if child == 0:
        os.close(writer)
        helper(reader)
    os.close(reader)
    try:
        os.write(writer, envelope(os.getpid()))
    except OSError:
        pass
    os.close(writer)
    return os.waitstatus_to_exitcode(os.waitpid(child, 0)[1])


def below_sudo(kind):
    reader, writer = channel(kind)
    hold_r, hold_w = os.pipe()
    parent = os.getpid()
    if os.fork() == 0:
        os.close(writer)
        os.close(hold_w)
        time.sleep(1)
        with open(f"/proc/{os.getppid()}/comm") as comm:
            sys.stdout.write(f"parent {os.getppid() == parent} {comm.read().strip()}\n")
            sys.stdout.flush()
        helper(reader)
    if os.fork() == 0:
        os.close(reader)
        os.close(hold_r)
        time.sleep(2)
        try:
            os.write(writer, envelope(parent))
        except OSError:
            pass
        os.close(writer)
        time.sleep(2)
        os.close(hold_w)
        os._exit(0)
    os.close(reader)
    os.close(writer)
    os.close(hold_w)
    os.dup2(hold_r, 0)
    os.execvp("sudo", ["sudo", "-S", "-p", "", "-l"])


mode, kind = sys.argv[1], sys.argv[2]
if mode == "direct":
    print(direct(kind))
else:
    below_sudo(kind)
PY

for helper_case in direct:socket direct:pipe below:socket below:pipe; do
  begin "helper-mode-refuses-${helper_case/:/-}" && {
    rm -f /etc/helper-marker
    run ivan "python3 $WORK/helper-mode.py ${helper_case%%:*} ${helper_case#*:}; sleep 4"
    if [[ $helper_case == direct:* ]]; then
      expect_out_line 1
    else
      expect_out_line 'parent True sudo'
    fi
    expect_err_has 'usage: sudo'
    expect_err_lacks 'lean-sudo-helper-1'
    [[ -e /etc/helper-marker ]] && fail "helper plan was executed with root privileges"
    rm -f /etc/helper-marker
    end
  }
done
