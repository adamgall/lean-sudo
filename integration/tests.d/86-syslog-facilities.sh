# Facility names and emitted priorities are pinned to the installed sudo.ws.
# Invalid Defaults remain fatal in lean-sudo (the documented fail-closed policy),
# while sudo.ws reports the same invalid-value diagnostic and continues.
syslog_facility_probe() {
  python3 - "$1" <<'PY'
import filecmp
import os
import pathlib
import re
import socket
import subprocess
import sys
import tempfile

facility = sys.argv[1]
accepted = dict(authpriv=10, auth=4, daemon=3, user=1)
accepted.update(("local" + str(n), 16 + n) for n in range(8))
policy = pathlib.Path("/etc/sudoers")
policy.write_text("Defaults !authenticate, !use_pty, !pam_session, "
                  "!log_exit_status, log_allowed, syslog=" + facility +
                  ", syslog_goodpri=notice\nroot ALL=(ALL:ALL) NOPASSWD: ALL\n")
policy.chmod(0o440)
saved = None
sock = socket.socket(socket.AF_UNIX, socket.SOCK_DGRAM)
try:
    if os.path.lexists("/dev/log"):
        fd, saved = tempfile.mkstemp(prefix="syslog-facility-", dir="/dev")
        os.close(fd)
        os.replace("/dev/log", saved)
    sock.bind("/dev/log")
    sock.settimeout(0.1)
    results = []
    for binary in ("/usr/bin/sudo.ws", "/usr/bin/sudo"):
        result = subprocess.run(
            ["/bin/bash", "-c", 'exec -a sudo "$@"', "sh", binary,
             "-n", "/usr/bin/printf", "facility-command-ran"],
            stdin=subprocess.DEVNULL, stdout=subprocess.PIPE,
            stderr=subprocess.PIPE, cwd="/", timeout=20)
        messages = []
        while True:
            try:
                text = sock.recv(65536).decode()
            except socket.timeout:
                break
            # Normalize only transport time and PID; retain facility and payload.
            text = re.sub(
                r"^(<\d+>)[A-Z][a-z]{2} [ 0-9][0-9] \d\d:\d\d:\d\d "
                r"sudo(?:\[\d+\])?: ", r"\1sudo: ", text)
            messages.append(text)
        results.append((result.returncode, result.stdout, result.stderr, messages))
    reference, actual = results
    if facility in accepted:
        assert reference == actual, results
        assert actual[:3] == (0, b"facility-command-ran", b""), actual
        command_logs = [m for m in actual[3] if "COMMAND=" in m]
        assert len(command_logs) == 1, actual
        assert command_logs[0].startswith("<" + str(accepted[facility] * 8 + 5) + ">"), actual
    else:
        diagnostic = ('value "' + facility + '" is invalid for option "syslog"').encode()
        assert reference[0] == 0 and reference[1] == b"facility-command-ran", reference
        assert diagnostic in reference[2] and diagnostic in actual[2], results
        if filecmp.cmp("/usr/bin/sudo", "/usr/bin/sudo.ws", shallow=False):
            assert actual[:3] == reference[:3], results
        else:
            assert actual[0] == 1 and actual[1] == b"", actual
            assert not any("COMMAND=" in m for m in actual[3]), actual
    print(facility + ": reference-backed facility check passed")
finally:
    sock.close()
    if os.path.lexists("/dev/log"):
        os.unlink("/dev/log")
    if saved is not None:
        os.replace(saved, "/dev/log")
PY
}

for syslog_facility in authpriv auth daemon user local{0..7} cron kern lpr mail news syslog uucp ftp; do
  begin "syslog-facility-$syslog_facility" && {
    syslog_facility_probe "$syslog_facility" >"$WORK/syslog-facility-result" 2>&1 ||
      fail "$(cat "$WORK/syslog-facility-result")"
    cat "$WORK/syslog-facility-result" >>"$LOG"
    end
  }
done
