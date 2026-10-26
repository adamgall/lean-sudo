cat >"$WORK/expects-signal.sh" <<'EOF'
trap 'echo got signal && exit 0' $@
for _ in $(seq 1 20); do
	sleep 0.1
done
echo >&2 received no signal
exit 1
EOF
chmod 0644 "$WORK/expects-signal.sh"

ext_signal_case() {
  local name=$1 mode=$2 pty_default=$3 prelude=$4
  begin "$name" && {
    printf 'Defaults %s\n' "$pty_default" | install -m 0440 /dev/stdin /etc/sudoers.d/ext-exec
    local snippet="sudo -n sh $WORK/expects-signal.sh HUP TERM & pid=\$!; sleep 0.8;"
    snippet+=" $prelude kill -ALRM \$pid; wait \$pid; echo rc=\$?"
    "$mode" root "$snippet"
    expect_rc 0
    expect_out_line 'got signal'
    expect_out_line 'rc=0'
    expect_out_lacks 'received no signal'
    expect_err_lacks 'received no signal'
    [[ $mode == pty || -z $ERR ]] || fail "stderr: expected empty"
    end
  }
}

ext_signal_case ext-exec-sigalrm-terminates-command-no-tty run use_pty ''
ext_signal_case ext-exec-sigchld-is-ignored-no-tty run use_pty 'kill -CHLD $pid; sleep 0.2;'
ext_signal_case ext-exec-sigalrm-terminates-command-pty pty use_pty ''
ext_signal_case ext-exec-sigchld-is-ignored-pty pty use_pty 'kill -CHLD $pid; sleep 0.2;'
ext_signal_case ext-exec-sigalrm-terminates-command-tty-no-pty pty '!use_pty' ''
ext_signal_case ext-exec-sigchld-is-ignored-tty-no-pty pty '!use_pty' 'kill -CHLD $pid; sleep 0.2;'

cat >"$WORK/pty-processes.sh" <<'EOF'
m=$PPID
o=$(ps -o ppid= -p "$m" | tr -d ' ')
field() { ps -o "$1=" -p "$2" | tr -d ' '; }
cmp -s "/proc/$m/cmdline" "/proc/$o/cmdline" && echo same-cmdline
echo "monitor-comm=$(cat "/proc/$m/comm")"
echo "monitor-args=$(ps -o args= -p "$m")"
echo "original-args=$(ps -o args= -p "$o")"
[ "$(field sid "$m")" = "$m" ] && echo monitor-session-leader
[ "$(field tty "$m")" = "$(field tty $$)" ] && echo monitor-command-same-tty
[ "$(field tty "$o")" != "$(field tty "$m")" ] && echo original-other-tty
case $(field stat $$) in *+*) echo command-foreground ;; esac
case $(field stat "$o") in *+*) echo original-foreground ;; esac
case $(field stat "$m") in *+*) echo monitor-foreground ;; esac
EOF
chmod 0644 "$WORK/pty-processes.sh"

begin ext-exec-pty-monitor-process-title && {
  printf 'Defaults use_pty\n' | install -m 0440 /dev/stdin /etc/sudoers.d/ext-exec
  pty root "sudo -n sh $WORK/pty-processes.sh"
  expect_rc 0
  expect_out_line same-cmdline
  expect_out_line 'monitor-comm=sudo'
  expect_out_line "monitor-args=sudo -n sh $WORK/pty-processes.sh"
  expect_out_line "original-args=sudo -n sh $WORK/pty-processes.sh"
  expect_out_line monitor-session-leader
  expect_out_line monitor-command-same-tty
  expect_out_line original-other-tty
  expect_out_line command-foreground
  expect_out_line original-foreground
  expect_out_lacks monitor-foreground
  expect_out_lacks lean-sudo-helper
  end
}

begin ext-exec-pty-owner-is-runas-user && {
  printf 'Defaults use_pty\nivan ALL=(ALL:ALL) NOPASSWD: ALL\n' |
    install -m 0440 /dev/stdin /etc/sudoers.d/ext-exec
  pty ivan "sudo -n -u judy sh -c 'stat -c \"%U %G %a\" \"\$(tty)\"'"
  expect_rc 0
  expect_out_line 'judy tty 620'
  end
}

cat >"$WORK/foreign-pty.py" <<'PY'
import os
import subprocess
import sys

own = os.ttyname(0)
master, slave = os.openpty()
foreign = os.ttyname(slave)
report = "/tmp/ext-exec-fds"
probe = ("fds=$(readlink /proc/$$/fd/0 /proc/$$/fd/1 /proc/$$/fd/2); "
         "echo $fds $(ps -o tty= -p $$) >%s" % report)


def label(path, new):
    if path == own:
        return "own"
    if path == foreign:
        return "foreign"
    if path == new:
        return "new"
    return "other"


for case, fds in (("own-out-foreign-err", (0, 1, slave)),
                  ("foreign-out-own-err", (slave, slave, 2)),
                  ("all-foreign", (slave, slave, slave))):
    subprocess.run(["sudo", "-n", "sh", "-c", probe],
                   stdin=fds[0], stdout=fds[1], stderr=fds[2], check=True)
    with open(report) as stream:
        lines = stream.read().split()
    os.unlink(report)
    terminal = "/dev/" + lines[3]
    new = terminal if terminal not in (own, foreign) else None
    print(case, " ".join(label(path, new) for path in lines[:3]),
          "ctty=" + label(terminal, new), flush=True)
PY
chmod 0644 "$WORK/foreign-pty.py"

begin ext-exec-foreign-tty-is-inherited && {
  printf 'Defaults use_pty\n' | install -m 0440 /dev/stdin /etc/sudoers.d/ext-exec
  pty root "python3 $WORK/foreign-pty.py"
  expect_rc 0
  expect_out_line 'own-out-foreign-err new new foreign ctty=new'
  expect_out_line 'foreign-out-own-err foreign foreign new ctty=new'
  expect_out_line 'all-foreign foreign foreign foreign ctty=new'
  end
}

cat >"$WORK/helper-marker.py" <<'PY'
import json
import os
import socket
import sys
import time

marker = "/etc/ext-exec-helper-marker"


def envelope(parent):
    plan = {"uid": 0, "gid": 0, "groups": [], "path": marker}
    data = {"magic": "lean-sudo-helper-1", "parent": parent, "effectiveUid": 0,
            "mask": 0, "name": "pam-admin", "payload": plan}
    return json.dumps(data).encode()


def forged(fd):
    os.dup2(fd, 63, inheritable=True)
    env = dict(os.environ, LEAN_SUDO_HELPER="63")
    os.execvpe("sudo", ["sudo", "-n", "/usr/bin/id", "-un"], env)


left, right = socket.socketpair()
reader, writer = left.detach(), right.detach()
if sys.argv[1] == "direct":
    child = os.fork()
    if child == 0:
        os.close(writer)
        forged(reader)
    os.close(reader)
    try:
        os.write(writer, envelope(os.getpid()))
    except OSError:
        pass
    os.close(writer)
    print("status", os.waitstatus_to_exitcode(os.waitpid(child, 0)[1]), flush=True)
    sys.exit(0)
hold_r, hold_w = os.pipe()
parent = os.getpid()
if os.fork() == 0:
    os.close(writer)
    os.close(hold_w)
    time.sleep(1)
    print("parent", os.getppid() == parent, flush=True)
    forged(reader)
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
os.execvp("sudo", ["sudo", "-S", "-p", "", "-u", "judy", "/usr/bin/id"])
PY
chmod 0644 "$WORK/helper-marker.py"

for helper_case in direct below; do
  begin "ext-exec-helper-marker-forged-$helper_case" && {
    rm -f /etc/ext-exec-helper-marker
    printf 'ivan ALL=(root) NOPASSWD: /usr/bin/id\n' |
      install -m 0440 /dev/stdin /etc/sudoers.d/ext-exec
    run ivan "python3 $WORK/helper-marker.py $helper_case; sleep 4"
    expect_out_line root
    if [[ $helper_case == direct ]]; then
      expect_out_line 'status 0'
    else
      expect_out_line 'parent True'
    fi
    expect_err_lacks 'lean-sudo-helper-1'
    [[ -e /etc/ext-exec-helper-marker ]] && fail "forged helper plan ran with root privileges"
    rm -f /etc/ext-exec-helper-marker
    end
  }
done

cat >"$WORK/root-peer-listener.py" <<'PY'
import os
import socket
import sys

path = sys.argv[1]
server = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
server.bind(path)
os.chmod(path, 0o777)
server.listen(1)
print("ready", flush=True)
conn, _ = server.accept()
conn.recv(1)
PY
cat >"$WORK/root-peer-marker.py" <<'PY'
import os
import socket
import sys

client = socket.socket(socket.AF_UNIX, socket.SOCK_STREAM)
client.connect(sys.argv[1])
os.dup2(client.detach(), 63, inheritable=True)
env = dict(os.environ, LEAN_SUDO_HELPER="63")
os.execvpe("sudo", ["sudo", "-n", "/usr/bin/id", "-un"], env)
PY
chmod 0644 "$WORK/root-peer-listener.py" "$WORK/root-peer-marker.py"

begin ext-exec-helper-marker-root-peer-runs-normally && {
  printf 'ivan ALL=(root) NOPASSWD: /usr/bin/id\n' |
    install -m 0440 /dev/stdin /etc/sudoers.d/ext-exec
  rm -f /run/ext-exec-root-peer.sock
  python3 "$WORK/root-peer-listener.py" /run/ext-exec-root-peer.sock >"$WORK/listener.out" &
  listener=$!
  for _ in $(seq 50); do grep -q ready "$WORK/listener.out" && break; sleep 0.1; done
  run ivan "python3 $WORK/root-peer-marker.py /run/ext-exec-root-peer.sock"
  kill "$listener" 2>/dev/null; wait "$listener" 2>/dev/null
  rm -f /run/ext-exec-root-peer.sock
  expect_rc 0
  expect_out_line root
  end
}

for group_case in "'#0':ivan:0" "ivan:adm:4"; do
  IFS=: read -r ext_user ext_group ext_gid <<<"$group_case"
  begin "ext-exec-runas-group-joins-groups-${ext_group}" && {
    printf 'ivan ALL=(ALL:ALL) NOPASSWD: ALL\n' | install -m 0440 /dev/stdin /etc/sudoers.d/ext-exec
    run ivan "sudo -n -u $ext_user -g $ext_group /usr/bin/python3 -c 'import os; print(os.getegid(), sorted(os.getgroups()))'"
    ivan_gid=$(gid_of ivan)
    if [[ $ext_group == ivan ]]; then
      expected="$ivan_gid [0, $ivan_gid]"
    else
      expected="4 [4, $ivan_gid]"
    fi
    expect_rc 0
    expect_out_line "$expected"
    end
  }
done

cat >/usr/local/bin/ext-exec-fd-script <<'EOF2'
#!/bin/sh
echo "argv0=$0"
ls /proc/$$/fd | sort -n | tr '\n' ' '
echo
EOF2
chmod 0755 /usr/local/bin/ext-exec-fd-script

for fd_case in plain:"" inherited:"exec 4</etc/hostname;"; do
  begin "ext-exec-digest-descriptor-number-${fd_case%%:*}" && {
    digest=$(sha384sum /usr/local/bin/ext-exec-fd-script | cut -d' ' -f1)
    printf 'Defaults !use_pty\nivan ALL=(ALL:ALL) NOPASSWD: sha384:%s /usr/local/bin/ext-exec-fd-script\n' \
      "$digest" | install -m 0440 /dev/stdin /etc/sudoers.d/ext-exec
    run ivan "${fd_case#*:} sudo -n /usr/local/bin/ext-exec-fd-script"
    expect_rc 0
    if [[ ${fd_case%%:*} == plain ]]; then
      expect_out_line 'argv0=/dev/fd/6'
      expect_out_line '0 1 2 6 10 '
    else
      expect_out_line 'argv0=/dev/fd/7'
      expect_out_line '0 1 2 7 10 '
    fi
    end
  }
done
