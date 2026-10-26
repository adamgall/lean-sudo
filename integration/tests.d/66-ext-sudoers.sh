ext_policy() {
  printf "$1" >/etc/sudoers.d/66-ext
  chown root:root /etc/sudoers.d/66-ext
  chmod 0440 /etc/sudoers.d/66-ext
}

ext_is_reference() { cmp -s /usr/bin/sudo /usr/bin/sudo.ws; }

ext_err_is() {
  [[ $ERR == "$1" ]] || fail "stderr: expected exactly '$1'"
}

ext_nul_rejected() {
  local name=$1 policy=$2 column=$3 command=$4
  begin "$name" && {
    ext_policy "$policy"
    run ivan "$command"
    expect_rc 1
    expect_out_empty
    expect_err_has "/etc/sudoers.d/66-ext:1:$column: syntax error"
    run root 'od -An -c /etc/sudoers.d/66-ext'
    expect_out_has '\0'
    end
  }
}

ext_nul_rejected ext-sudoers-nul-username 'ivan\0 ALL=(ALL:ALL) NOPASSWD: ALL\n' 5 'sudo -n id -u'
ext_nul_rejected ext-sudoers-nul-username-suffix 'ivan\0evil ALL=(ALL:ALL) NOPASSWD: ALL\n' 5 \
  'sudo -n id -u'
ext_nul_rejected ext-sudoers-nul-other-username 'nobody\0ivan ALL=(ALL:ALL) NOPASSWD: ALL\n' 7 \
  'sudo -n id -u'
ext_nul_rejected ext-sudoers-nul-runas-user 'ivan ALL=(root\0:ALL) NOPASSWD: ALL\n' 15 \
  'sudo -n id -u'
ext_nul_rejected ext-sudoers-nul-runas-user-suffix 'ivan ALL=(root\0evil:ALL) NOPASSWD: ALL\n' 15 \
  'sudo -n id -u'
ext_nul_rejected ext-sudoers-nul-runas-group 'ivan ALL=(ALL:root\0) NOPASSWD: ALL\n' 19 \
  'sudo -n -g root id -g'

begin ext-sudoers-nul-trailing-and-comment && {
  ext_policy 'ivan ALL=(ALL:ALL) NOPASSWD: ALL\0\n# comment\0tail\n'
  run ivan 'sudo -n id -u'
  expect_rc 0
  expect_out_line 0
  ext_err_is ''
  end
}

ext_cwd_rejected() {
  local name=$1 value=$2
  begin "$name" && {
    ext_policy "ivan ALL=(ALL:ALL) CWD=$value NOPASSWD: ALL\n"
    run ivan 'cd / && sudo -n pwd'
    expect_rc 1
    expect_out_empty
    expect_err_has \
      "/etc/sudoers.d/66-ext:1:24: values for \"CWD\" must start with a '/', '~', or '*'"
    expect_err_lacks 'syntax error'
    end
  }
}

ext_cwd_rejected ext-sudoers-cwd-relative usr
ext_cwd_rejected ext-sudoers-cwd-dot-slash ./usr

begin ext-sudoers-defaults-unknown-located && {
  ext_policy 'Defaults !unsupported\nivan ALL=(ALL:ALL) NOPASSWD: ALL\n'
  run ivan 'sudo -n true'
  expect_rc 0
  ext_err_is '/etc/sudoers.d/66-ext:1:11: unknown defaults entry "unsupported"'
  end
}

begin ext-sudoers-defaults-unknown-then-invalid && {
  ext_policy 'Defaults !unsupported\nDefaults !passwd_tries\nivan ALL=(ALL:ALL) NOPASSWD: ALL\n'
  run ivan 'sudo -n true'
  if ext_is_reference; then expect_rc 0; else expect_rc 1; fi
  ext_err_is '/etc/sudoers.d/66-ext:1:11: unknown defaults entry "unsupported"
/etc/sudoers.d/66-ext:2:11: no value specified for "passwd_tries"'
  end
}

begin ext-sudoers-defaults-diagnostic-order && {
  ext_policy 'Defaults !passwd_tries\nDefaults !unsupported\nDefaults fqdn=1\n'
  printf 'ivan ALL=(ALL:ALL) NOPASSWD: ALL\n' >>/etc/sudoers.d/66-ext
  run ivan 'sudo -n true'
  if ext_is_reference; then expect_rc 0; else expect_rc 1; fi
  ext_err_is '/etc/sudoers.d/66-ext:3:15: option "fqdn" does not take a value
/etc/sudoers.d/66-ext:1:11: no value specified for "passwd_tries"
/etc/sudoers.d/66-ext:2:11: unknown defaults entry "unsupported"'
  end
}

begin ext-sudoers-main-file-missing && {
  cp -a /etc/nsswitch.conf "$WORK/66-ext-nsswitch"
  sed -i 's/^sudoers:.*/sudoers: files/' /etc/nsswitch.conf
  rm -f /etc/sudoers
  run root 'sudo -n true'
  cp -a "$WORK/66-ext-nsswitch" /etc/nsswitch.conf
  expect_rc 1
  expect_out_empty
  ext_err_is 'sudo: unable to open /etc/sudoers: No such file or directory
sudo: error initializing audit plugin sudoers_audit'
  end
}

begin ext-sudoers-sudo-conf-nul-ends-line && {
  cp -a /etc/sudo.conf "$WORK/66-ext-sudo.conf"
  printf '#!/bin/sh\necho ivanpw\n' >"$WORK/66-ext-askpass"
  chmod 0755 "$WORK/66-ext-askpass"
  printf 'Path askpass %s\0 # \\\nPath askpass /nonexistent-66-ext-askpass\n' \
    "$WORK/66-ext-askpass" >/etc/sudo.conf
  ext_policy 'ivan ALL=(ALL:ALL) /usr/bin/id\n'
  run ivan 'sudo -A /usr/bin/id -u'
  cp -a "$WORK/66-ext-sudo.conf" /etc/sudo.conf
  expect_rc 0
  expect_out_line 0
  end
}

begin ext-sudoers-timestamp-alerts-logged && {
  ext_ts_out=$WORK/66-ext-ts-alert.out
  python3 - "$WORK" >"$ext_ts_out" 2>&1 <<'PY' || fail "$(cat "$ext_ts_out")"
import pathlib
import time
import pwd
import re
import shutil
import struct
import subprocess
import sys
sys.path.insert(0, "/usr/local/lib")
from sudo_it_logging import Syslog

user = pwd.getpwnam("ivan")
base = pathlib.Path(sys.argv[1]) / "66-ext-ts-alert"
policy = pathlib.Path("/etc/sudoers.d/66-ext")
record = base / "ts" / str(user.pw_uid)


def entry(kind, uid, seconds):
    return struct.pack("<HHHHIiqqqqq", 2, 56, kind, 0, uid, 0, 0, 0, seconds, 0, 0)


def directory_record():
    record.mkdir()
    record.chmod(0o700)


def future_record():
    record.write_bytes(entry(4, 0, 0) + entry(1, user.pw_uid, 10 ** 12))
    record.chmod(0o600)


mailbox = pathlib.Path("/var/mail/root")


def mails():
    pattern = re.compile(r"^\S+ : [A-Z][a-z]{2} [ 0-9]{2} [0-9:]{8} : (.*)$", re.M)
    deadline = time.monotonic() + 15
    while True:
        text = mailbox.read_text() if mailbox.exists() else ""
        found = sorted(match.group(1) for match in pattern.finditer(text))
        if len(found) >= 2 or time.monotonic() > deadline:
            break
        time.sleep(.05)
    time.sleep(1)
    text = mailbox.read_text() if mailbox.exists() else ""
    return sorted(match.group(1) for match in pattern.finditer(text))


def run(binary, setup):
    mailbox.unlink(missing_ok=True)
    shutil.rmtree(base, ignore_errors=True)
    record.parent.mkdir(parents=True)
    base.chmod(0o755)
    record.parent.chmod(0o700)
    setup()
    policy.write_text("Defaults:ivan lecture=never, timestamp_type=global, timestampdir="
                      + str(record.parent) + "\nivan ALL=(ALL) ALL\n")
    policy.chmod(0o440)
    with Syslog() as logger:
        result = subprocess.run(
            ["setpriv", "--reuid=" + str(user.pw_uid), "--regid=" + str(user.pw_gid),
             "--init-groups", "--", "/bin/bash", "-c", 'exec -a sudo "$@"', "sh", binary,
             "-n", "/usr/bin/true"],
            env={"PATH": "/usr/bin:/bin", "HOME": user.pw_dir, "USER": "ivan",
                 "LOGNAME": "ivan", "LANG": "C.UTF-8"},
            stdin=subprocess.DEVNULL, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
            cwd="/", timeout=20)
        messages = [re.sub(r"^(<\d+>)[A-Z][a-z]{2} [ 0-9][0-9] \d\d:\d\d:\d\d "
                           r"sudo(?:\[\d+\])?: ", r"\1sudo: ", text)
                    for text in logger.messages()]
    state = record.read_bytes()[:112] if record.is_file() else b"directory"
    return (result.returncode, result.stdout,
            result.stderr.replace(b"sudo.ws", b"sudo"), messages, state, mails())


cases = [(directory_record, "ivan : unable to open %s : Is a directory ; " % record),
         (future_record, "ivan : ignoring time stamp from the future ; ")]
for setup, expected in cases:
    reference, actual = (run(binary, setup) for binary in ("/usr/bin/sudo.ws", "/usr/bin/sudo"))
    assert reference == actual, (reference, actual)
    assert any(expected in text for text in actual[3]), actual
    assert any(expected in text for text in actual[5]), actual
    print("timestamp alert matches sudo.ws:", actual)
shutil.rmtree(base, ignore_errors=True)
PY
  cat "$ext_ts_out" >>"$LOG"
  end
}

ext_include_missing() {
  local name=$1 include=$2 path=$3
  begin "$name" && {
    ext_policy "@include $include\n"
    run ivan 'sudo -n true'
    expect_rc 1
    expect_out_empty
    expect_err_has "sudo: unable to open $path: No such file or directory"
    expect_err_lacks "unable to open $path: unable to open"
    end
  }
}

ext_include_missing ext-sudoers-include-missing /etc/66-ext-missing /etc/66-ext-missing
ext_include_missing ext-sudoers-include-grandparent-missing ../../66-ext-missing \
  /etc/sudoers.d/../../66-ext-missing

ext_env_order() {
  local name=$1 policy=$2 kept=$3 dropped=$4
  begin "$name" && {
    ext_policy "$policy"
    XENV=(FOO=foo BAR=bar)
    run ivan 'sudo -n /usr/bin/env'
    expect_rc 0
    expect_out_line "$kept"
    expect_out_lacks "$dropped"
    end
  }
}

EXT_ENV_RULE='ivan ALL=(ALL:ALL) NOPASSWD: /usr/bin/env\n'
EXT_RUNAS_BOTH='Defaults>root env_keep = "BAR FOO"\n'
ext_env_order ext-sudoers-defaults-order-host-last \
  "${EXT_RUNAS_BOTH}Defaults:ivan env_keep = FOO\nDefaults@ALL env_keep = BAR\n$EXT_ENV_RULE" \
  BAR=bar FOO=foo
ext_env_order ext-sudoers-defaults-order-user-last \
  "${EXT_RUNAS_BOTH}Defaults@ALL env_keep = BAR\nDefaults:ivan env_keep = FOO\n$EXT_ENV_RULE" \
  FOO=foo BAR=bar
ext_env_order ext-sudoers-defaults-order-runas-after-user \
  "Defaults:ivan env_keep = FOO\nDefaults>root env_keep = BAR\n$EXT_ENV_RULE" \
  BAR=bar FOO=foo
ext_env_order ext-sudoers-defaults-order-cmnd-last \
  "Defaults!/usr/bin/env env_keep = FOO\nDefaults>root env_keep = BAR\n$EXT_ENV_RULE" \
  FOO=foo BAR=bar

ext_runas_default() {
  local name=$1 policy=$2 command=$3 user=$4 home=$5
  begin "$name" && {
    ext_policy "$policy"
    run ivan "$command"
    expect_rc 0
    expect_out_line "USER=$user"
    expect_out_line "HOME=$home"
    end
  }
}

ext_runas_default ext-sudoers-runas-default-runas-scope \
  "Defaults>root runas_default=judy\n$EXT_ENV_RULE" 'sudo -n /usr/bin/env' judy /home/judy
ext_runas_default ext-sudoers-runas-default-runas-scope-initial-user \
  "Defaults>root runas_default=judy\nDefaults>judy runas_default=kate\n$EXT_ENV_RULE" \
  'sudo -n /usr/bin/env' judy /home/judy
ext_runas_default ext-sudoers-runas-default-cmnd-scope \
  "Defaults!/usr/bin/env runas_default=judy\n$EXT_ENV_RULE" 'sudo -n /usr/bin/env' judy /home/judy
ext_runas_default ext-sudoers-runas-default-explicit-user-wins \
  "Defaults!/usr/bin/env runas_default=judy\nDefaults>root runas_default=kate\n$EXT_ENV_RULE" \
  'sudo -n -u root /usr/bin/env' root /root

EXT_NEGATED_NETGROUP_RULE='ivan ALL=(ALL, !+extrunas) NOPASSWD: /usr/bin/env\n'
ext_runas_netgroup() {
  local name=$1 member=$2 rc=$3
  begin "$name" && {
    cp -a /etc/nsswitch.conf "$WORK/66-ext-nsswitch"
    printf 'passwd: files\ngroup: files\nshadow: files\nhosts: files dns\nnetgroup: files\n' \
      >/etc/nsswitch.conf
    printf 'extrunas (,%s,)\n' "$member" >/etc/netgroup
    ext_policy "Defaults!/usr/bin/env runas_default=judy\n$EXT_NEGATED_NETGROUP_RULE"
    run ivan "printf 'ivanpw\\n' | sudo -S /usr/bin/env"
    cp -a "$WORK/66-ext-nsswitch" /etc/nsswitch.conf
    rm -f /etc/netgroup
    expect_rc "$rc"
    if [[ $rc == 0 ]]; then
      expect_out_line USER=judy
    else
      expect_out_empty
      expect_err_has "user ivan is not allowed to execute '/usr/bin/env' as judy"
    fi
    end
  }
}

ext_runas_netgroup ext-sudoers-runas-default-cmnd-negated-netgroup-denies judy 1
ext_runas_netgroup ext-sudoers-runas-default-cmnd-negated-netgroup-other kate 0

begin ext-sudoers-nul-inside-comment-ignored && {
  printf '# note\000 trailing comment text\nivan ALL=(root) NOPASSWD: /usr/bin/id\n' |
    install -m 0440 /dev/stdin /etc/sudoers.d/ext-sudoers
  run ivan 'sudo -n /usr/bin/id -un'
  expect_rc 0
  expect_out_line root
  expect_err_lacks 'syntax error'
  end
}
