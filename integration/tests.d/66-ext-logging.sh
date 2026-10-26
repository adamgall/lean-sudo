EXT_LOG=/var/log/ext-logging.log

ext_logging_lines() {
  run root "sed -E 's/^[A-Z][a-z]{2} [ 0-9]{2} [0-9:]{8} : //' $EXT_LOG"
}

ext_logging_sudoers() {
  rm -f /etc/sudoers.d/ext-logging
  install -m 0440 /dev/stdin /etc/sudoers.d/ext-logging
}

ext_logging_mails() {
  cat >"$WORK/ext-logging-mail.py" <<'PY'
import pathlib, re, sys, time
want = int(sys.argv[1])
box = pathlib.Path("/var/mail/root")
deadline = time.monotonic() + 15
def count():
    return box.read_text().count("Auto-Submitted: auto-generated") if box.exists() else 0
while count() < want:
    assert time.monotonic() < deadline, "mail delivery timed out: %d of %d" % (count(), want)
    time.sleep(.05)
time.sleep(1)
text = box.read_text() if box.exists() else ""
print("mails=%d" % text.count("Auto-Submitted: auto-generated"))
for line in text.splitlines():
    match = re.match(r"^\S+ : [A-Z][a-z]{2} [ 0-9]{2} [0-9:]{8} : (.*)$", line)
    if match:
        print(match.group(1))
PY
  run root "python3 '$WORK/ext-logging-mail.py' $1"
}

begin ext-logging-logfile-created-root-group && {
  rm -f "$EXT_LOG"
  ext_logging_sudoers <<EOF
Defaults logfile=$EXT_LOG, loglinelen=0
ivan ALL=(ALL:ALL) NOPASSWD: ALL
EOF
  run ivan 'umask 0277; sudo -n /usr/bin/true'
  expect_rc 0
  run root "stat -c '%u:%g %a' $EXT_LOG"
  expect_out_line '0:0 600'
  rm -f "$EXT_LOG"
  ext_logging_sudoers <<EOF
Defaults logfile=$EXT_LOG, log_format=json
ivan ALL=(ALL:ALL) NOPASSWD: ALL
EOF
  run ivan 'umask 0; sudo -n /usr/bin/true'
  expect_rc 0
  run root "stat -c '%u:%g %a' $EXT_LOG"
  expect_out_line '0:0 600'
  rm -f "$EXT_LOG"
  end
}

begin ext-logging-shell-command-escaped && {
  rm -f "$EXT_LOG"
  ext_logging_sudoers <<EOF
Defaults logfile=$EXT_LOG, loglinelen=0, log_exit_status
kate ALL=(ALL:ALL) NOPASSWD: ALL
liam ALL=(ALL:ALL) NOPASSWD: /usr/bin/id
EOF
  run kate "sudo -n -s /bin/echo 'a b' \"c'd\""
  expect_rc 0
  run kate 'sudo -n -i /usr/bin/true'
  expect_rc 0
  run liam 'sudo -n -i /usr/bin/true'
  expect_rc 1
  ext_logging_lines
  expect_out_line "kate : PWD=/home/kate ; USER=root ; COMMAND=/bin/bash -c '\\\\/bin\\\\/echo a\\\\ b c\\\\\\'d'"
  expect_out_line "kate : PWD=/home/kate ; USER=root ; COMMAND=/bin/bash -c '\\\\/bin\\\\/echo a\\\\ b c\\\\\\'d' ; EXIT=0"
  expect_out_line 'kate : PWD=/root ; USER=root ; COMMAND=/bin/bash --login -c \\/usr\\/bin\\/true'
  expect_out_line 'kate : PWD=/root ; USER=root ; COMMAND=/bin/bash --login -c \\/usr\\/bin\\/true ; EXIT=0'
  expect_out_line 'liam : a password is required ; PWD=/root ; USER=root ; COMMAND=/bin/bash -c \\/usr\\/bin\\/true'
  rm -f "$EXT_LOG"
  end
}

begin ext-logging-json-shell-runargv && {
  rm -f "$EXT_LOG"
  ext_logging_sudoers <<EOF
Defaults logfile=$EXT_LOG, log_format=json_compact
kate ALL=(ALL:ALL) NOPASSWD: ALL
liam ALL=(ALL:ALL) NOPASSWD: /usr/bin/id
EOF
  run kate 'sudo -n -i /usr/bin/true'
  expect_rc 0
  run liam 'sudo -n -i /usr/bin/true'
  expect_rc 1
  run root "python3 -c 'import json, sys
for line in open(sys.argv[1]):
    kind, event = next(iter(json.loads(line).items()))
    print(kind, event[\"submituser\"], event[\"command\"], json.dumps(event[\"runargv\"]))' $EXT_LOG"
  expect_rc 0
  expect_out_line 'accept kate /bin/bash ["-bash", "--login", "-c", "\\/usr\\/bin\\/true"]'
  expect_out_line 'reject liam /bin/bash ["/bin/bash", "-c", "\\/usr\\/bin\\/true"]'
  rm -f "$EXT_LOG"
  end
}

begin ext-logging-tsid-log-output && {
  rm -rf "$EXT_LOG" /var/log/sudo-io
  ext_logging_sudoers <<EOF
Defaults logfile=$EXT_LOG, loglinelen=0, log_exit_status
judy ALL=(ALL:ALL) NOPASSWD: LOG_OUTPUT: /usr/bin/true
judy ALL=(ALL:ALL) NOPASSWD: /usr/bin/id
EOF
  run judy 'sudo -n /usr/bin/true && sudo -n /usr/bin/id -u'
  expect_rc 0
  ext_logging_lines
  expect_out_line 'judy : PWD=/home/judy ; USER=root ; TSID=000001 ; COMMAND=/usr/bin/true'
  expect_out_line 'judy : PWD=/home/judy ; USER=root ; TSID=000001 ; COMMAND=/usr/bin/true ; EXIT=0'
  expect_out_line 'judy : PWD=/home/judy ; USER=root ; COMMAND=/usr/bin/id -u'
  rm -rf "$EXT_LOG" /var/log/sudo-io
  end
}

begin ext-logging-tsid-log-input-file && {
  rm -rf "$EXT_LOG" /var/log/sudo-io
  ext_logging_sudoers <<EOF
Defaults logfile=$EXT_LOG, loglinelen=0, log_input
Defaults:judy iolog_file=%{user}/session
kate ALL=(ALL:ALL) NOPASSWD: ALL
judy ALL=(ALL:ALL) NOPASSWD: ALL
EOF
  run kate 'sudo -n -g kate /usr/bin/true'
  expect_rc 0
  run judy 'sudo -n /usr/bin/true'
  expect_rc 0
  ext_logging_lines
  expect_out_line 'kate : PWD=/home/kate ; USER=kate ; GROUP=kate ; TSID=000001 ; COMMAND=/usr/bin/true'
  expect_out_line 'judy : PWD=/home/judy ; USER=root ; TSID=judy/session ; COMMAND=/usr/bin/true'
  rm -rf "$EXT_LOG" /var/log/sudo-io
  end
}

begin ext-logging-mail-always-exit-mail && {
  rm -f "$EXT_LOG"
  rm -f /var/mail/root
  ext_logging_sudoers <<EOF
Defaults mail_always, logfile=$EXT_LOG, loglinelen=0
ivan ALL=(ALL:ALL) NOPASSWD: ALL
EOF
  cat >"$WORK/ext-logging-syslog.py" <<'PY'
import subprocess, sys
sys.path.insert(0, "/usr/local/lib")
from sudo_it_logging import Syslog
with Syslog() as log:
    result = subprocess.run(["setpriv", "--reuid=ivan", "--regid=ivan", "--init-groups",
                             "sudo", "-n", "/bin/sh", "-c", "exit 3"],
                            cwd="/", stdin=subprocess.DEVNULL)
    print("rc=%d" % result.returncode)
    for message in log.messages():
        if "COMMAND=" in message:
            print("syslog:" + message.split("sudo:", 1)[1].strip())
PY
  run root "python3 '$WORK/ext-logging-syslog.py'"
  expect_rc 0
  expect_out_line 'rc=3'
  expect_out_line "syslog:ivan : PWD=/ ; USER=root ; COMMAND=/bin/sh -c 'exit 3'"
  expect_out_lacks 'EXIT='
  ext_logging_lines
  expect_out_line "ivan : PWD=/ ; USER=root ; COMMAND=/bin/sh -c 'exit 3'"
  expect_out_line "ivan : PWD=/ ; USER=root ; COMMAND=/bin/sh -c 'exit 3' ; EXIT=3"
  ext_logging_mails 2
  expect_rc 0
  expect_out_line 'mails=2'
  expect_out_line "ivan : PWD=/ ; USER=root ; COMMAND=/bin/sh -c 'exit 3'"
  expect_out_line "ivan : PWD=/ ; USER=root ; COMMAND=/bin/sh -c 'exit 3' ; EXIT=3"
  rm -f "$EXT_LOG"
  end
}

begin ext-logging-mail-always-without-syslog && {
  rm -f "$EXT_LOG"
  rm -f /var/mail/root
  ext_logging_sudoers <<EOF
Defaults mail_always, !syslog
ivan ALL=(ALL:ALL) NOPASSWD: ALL
EOF
  run ivan "sudo -n /bin/sh -c 'exit 4'"
  expect_rc 4
  ext_logging_sudoers <<EOF
Defaults mail_always, !syslog, logfile=$EXT_LOG, loglinelen=0
ivan ALL=(ALL:ALL) NOPASSWD: ALL
EOF
  run ivan "sudo -n /bin/sh -c 'exit 3'"
  expect_rc 3
  ext_logging_lines
  expect_out_line "ivan : PWD=/home/ivan ; USER=root ; COMMAND=/bin/sh -c 'exit 3'"
  expect_out_lacks 'EXIT='
  ext_logging_mails 2
  expect_rc 0
  expect_out_line 'mails=2'
  expect_out_line "ivan : PWD=/home/ivan ; USER=root ; COMMAND=/bin/sh -c 'exit 3'"
  expect_out_line "ivan : PWD=/home/ivan ; USER=root ; COMMAND=/bin/sh -c 'exit 3' ; EXIT=3"
  expect_out_lacks 'exit 4'
  rm -f "$EXT_LOG"
  end
}

begin ext-logging-mail-only-accept-logfile && {
  rm -f "$EXT_LOG"
  rm -f /var/mail/root
  ext_logging_sudoers <<EOF
Defaults mail_all_cmnds, !log_allowed, log_exit_status, logfile=$EXT_LOG, loglinelen=0
ivan ALL=(ALL:ALL) NOPASSWD: ALL
EOF
  run ivan "sudo -n /bin/sh -c 'exit 5'"
  expect_rc 5
  ext_logging_lines
  expect_out_line "ivan : PWD=/home/ivan ; USER=root ; COMMAND=/bin/sh -c 'exit 5'"
  expect_out_line "ivan : PWD=/home/ivan ; USER=root ; COMMAND=/bin/sh -c 'exit 5' ; EXIT=5"
  ext_logging_mails 1
  expect_rc 0
  expect_out_line 'mails=1'
  expect_out_lacks 'EXIT='
  rm -f "$EXT_LOG"
  end
}

begin ext-logging-version-logfile && {
  ext_logging_sudoers <<EOF
Defaults logfile=$EXT_LOG
EOF
  run root 'sudo -V'
  expect_rc 0
  expect_out_line "Path to log file: $EXT_LOG"
  [[ $(grep -A1 -F "Umask to use or 0777 to use user's:" <<<"$OUT" | tail -n1) == "Path to log file: $EXT_LOG" ]] ||
    fail 'stdout: expected the log file line right after the umask line'
  end
}

begin ext-logging-json-runenv-order && {
  rm -f "$EXT_LOG"
  ext_logging_sudoers <<EOF
Defaults logfile=$EXT_LOG, log_format=json_compact
ivan ALL=(ALL:ALL) NOPASSWD: ALL
EOF
  run ivan 'sudo -n /usr/bin/true'
  expect_rc 0
  run root "python3 -c 'import json, sys
for line in open(sys.argv[1]):
    kind, event = next(iter(json.loads(line).items()))
    print(kind, \" \".join(item.split(\"=\", 1)[0] for item in event[\"runenv\"]))' $EXT_LOG"
  expect_rc 0
  expect_out_line 'accept PATH LANG MAIL LOGNAME USER HOME SHELL TERM SUDO_COMMAND SUDO_USER SUDO_UID SUDO_GID SUDO_HOME'
  rm -f "$EXT_LOG"
  end
}
