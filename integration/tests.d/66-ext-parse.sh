ext_parse_file() {
  printf '%s' "$2" >"$1"
  chown root:root "$1"
  chmod 0440 "$1"
}

ext_parse_policy() { ext_parse_file /etc/sudoers.d/66-ext-parse "$1"; }

ext_parse_is_reference() { cmp -s /usr/bin/sudo /usr/bin/sudo.ws; }

ext_parse_matches_reference() {
  local command=$1 lean_rc=$RC lean_err=$ERR rest line
  run ivan "${command/sudo /sudo.ws }"
  local ref_err=$ERR
  RC=$lean_rc ERR=$lean_err
  [[ -n $ERR ]] || fail "stderr: expected sudo.ws parse diagnostics"
  if [[ $ref_err != "$ERR"* ]]; then
    fail "stderr: expected sudo.ws's diagnostics exactly:"$'\n'"$ref_err"
    return
  fi
  rest=${ref_err#"$ERR"}
  while IFS= read -r line; do
    [[ -z $line || $line == 'sudo: '* ]] || fail "stderr: missing sudo.ws diagnostic line '$line'"
  done <<<"$rest"
  ext_parse_is_reference || expect_rc 1
}

ext_parse_diagnostics() {
  local name=$1 policy=$2 command=$3 header=$4
  begin "$name" && {
    ext_parse_policy "$policy"
    run ivan "$command"
    expect_out_empty
    expect_err_has "$header"
    ext_parse_matches_reference "$command"
    end
  }
}

ext_parse_diagnostics ext-parse-error-token-column $'ivan ALL=(root NOPASSWD: ALL\n' \
  'sudo -n true' '/etc/sudoers.d/66-ext-parse:1:16: syntax error'
ext_parse_diagnostics ext-parse-errors-all-lines \
  $'Cmnd_Alias BROKEN =\nivan ALL=(ALL:AL L) NOPASSWD: ALL\nfoo bar\n' 'sudo -n true' \
  '/etc/sudoers.d/66-ext-parse:3:8: syntax error'
EXT_PARSE_UNDERSCORE=$'Cmnd_Alias _INVALID = /usr/bin/true\nivan ALL=(ALL:ALL) NOPASSWD: ALL\n'
EXT_PARSE_UNDERSCORE+=$'ALL ALL=(ALL:ALL) !_INVALID\n'
ext_parse_diagnostics ext-parse-alias-underscore "$EXT_PARSE_UNDERSCORE" 'sudo -n true' \
  '/etc/sudoers.d/66-ext-parse:3:20: expected a fully-qualified path name'
ext_parse_diagnostics ext-parse-escaped-command-path-rejected \
  $'ivan ALL=(ALL) NOPASSWD: /usr/bin/t\\rue\n' 'sudo -n /usr/bin/true' \
  '/etc/sudoers.d/66-ext-parse:1:26: expected a fully-qualified path name'
ext_parse_diagnostics ext-parse-escaped-defaults-command-path-rejected \
  $'Defaults!/usr/bin/\\true !lecture\n' 'sudo -n /usr/bin/true' \
  '/etc/sudoers.d/66-ext-parse:1:10: expected a fully-qualified path name'
ext_parse_diagnostics ext-parse-chroot-warning-between-errors \
  $'foo bar\nivan ALL=(ALL) CHROOT=/ NOPASSWD: ALL\nbaz qux\n' 'sudo -n true' \
  '/etc/sudoers.d/66-ext-parse:2:23: "CHROOT" is deprecated'
ext_parse_diagnostics ext-parse-include-loop \
  $'ivan ALL=(ALL) NOPASSWD: ALL\n@include /etc/sudoers.d/66-ext-parse\n' 'sudo -n true' \
  '/etc/sudoers.d/66-ext-parse: too many levels of includes'
ext_parse_diagnostics ext-parse-missing-include-then-error \
  $'@include /etc/66-ext-parse-missing\nfoo bar\n' 'sudo -n true' \
  'sudo: unable to open /etc/66-ext-parse-missing: No such file or directory'

begin ext-parse-include-errors-in-order && {
  ext_parse_file /etc/66-ext-parse-inc $'baz\nUser_Alias A = ivan\nUser_Alias A = judy\n'
  ext_parse_policy $'foo bar\n@include /etc/66-ext-parse-inc\nqux quux\n'
  run ivan 'sudo -n true'
  expect_out_empty
  expect_err_has '/etc/66-ext-parse-inc:3:20: duplicate User_Alias "A"'
  ext_parse_matches_reference 'sudo -n true'
  rm -f /etc/66-ext-parse-inc
  end
}

begin ext-parse-defaults-quoted-value-column && {
  EXT_PARSE_LOGFILE=$'Defaults logfile="\\/var/log/66-ext-parse.log"\n'
  ext_parse_policy "$EXT_PARSE_LOGFILE"$'ivan ALL=(ALL) NOPASSWD: ALL\n'
  run ivan 'sudo -n true'
  ext_parse_is_reference || expect_rc 1
  expect_out_empty
  expect_err_has $'/etc/sudoers.d/66-ext-parse:1:45: values for "logfile" must start with a \'/\''
  end
}

begin ext-parse-include-search-path-second-entry && {
  mkdir -p /tmp/66-ext-parse
  printf 'ivan ALL=(ALL) NOPASSWD: /usr/bin/true\n' >/tmp/66-ext-parse/rel
  chmod 0440 /tmp/66-ext-parse/rel
  ext_parse_policy $'@include /etc/66-ext-parse-missing:rel\n'
  run ivan 'cd /tmp/66-ext-parse && sudo -n /usr/bin/true'
  expect_rc 0
  expect_out_empty
  run ivan 'cd / && sudo -n /usr/bin/true'
  expect_rc 1
  expect_err_has \
    'sudo: unable to open /etc/66-ext-parse-missing:rel: No such file or directory'
  rm -rf /tmp/66-ext-parse
  end
}

ext_parse_log_script() {
  cat >"$WORK/66-ext-parse-log.py" <<'PY'
import pathlib, re, subprocess, sys, time
sys.path.insert(0, "/usr/local/lib")
from sudo_it_logging import Syslog

LOGFILE = pathlib.Path("/var/log/66-ext-parse.log")

def observe(binary):
    for box in pathlib.Path("/var/mail").glob("*"):
        box.unlink()
    LOGFILE.unlink(missing_ok=True)
    with Syslog() as log:
        subprocess.run(["setpriv", "--reuid=ivan", "--regid=ivan", "--init-groups",
                        binary, "-n", "/usr/bin/true"], cwd="/", stdin=subprocess.DEVNULL,
                       stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        deadline = time.monotonic() + 30
        time.sleep(0.5)
        while time.monotonic() < deadline:
            queued = subprocess.run(["exim", "-bpc"], capture_output=True, text=True).stdout
            if queued.strip() == "0":
                break
            time.sleep(0.2)
        time.sleep(0.5)
        records = [re.sub(r"^(<\d+>)\S+ +\d+ [\d:]+ ", r"\1", m) for m in log.messages()
                   if " sudo: " in m and "pam_unix" not in m and "COMMAND=" not in m]
    mails = []
    for box in sorted(pathlib.Path("/var/mail").glob("*")):
        for message in box.read_text().split("\nFrom ")[0:]:
            head, _, body = message.partition("\n\n")
            keep = [line for line in head.splitlines()
                    if line.startswith(("To:", "Subject:", "Auto-Submitted:"))]
            body = re.sub(r"[A-Z][a-z]{2} [ \d]\d [\d:]{8}", "TIME", body.strip())
            mails.append((box.name, keep, body))
    logged = []
    if LOGFILE.exists():
        logged = [re.sub(r"^[A-Z][a-z]{2} [ \d]\d [\d:]{8} : ", "", line)
                  for line in LOGFILE.read_text().splitlines()]
        LOGFILE.unlink()
    return records, mails, [line for line in logged if "COMMAND=" not in line]

lean = observe("/usr/bin/sudo")
reference = observe("/usr/bin/sudo.ws")
print("records=%d mails=%d logged=%d" % (len(lean[0]), len(lean[1]), len(lean[2])))
for line in lean[2]:
    print("logfile:" + line)
if lean[2] != reference[2]:
    print("logfile-mismatch")
for record in lean[0]:
    print("syslog:" + record)
if reference[0][:len(lean[0])] != lean[0]:
    print("syslog-mismatch")
    for record in reference[0]:
        print("reference:" + record)
for record in reference[0][len(lean[0]):]:
    if re.search(r"syntax error|unable to open|owned by|duplicate|invalid|unknown", record):
        print("syslog-missing:" + record)
if lean[1] != [m for m in reference[1] if "problem parsing sudoers" in m[2]]:
    print("mail-mismatch")
    print(repr(lean[1]))
    print(repr(reference[1]))
PY
}

ext_parse_logged() {
  local name=$1 policy=$2 records=$3 mails=$4
  begin "$name" && {
    ext_parse_policy "$policy"
    ext_parse_log_script
    run root "python3 '$WORK/66-ext-parse-log.py'"
    expect_rc 0
    expect_out_line "records=$records mails=$mails logged=${5:-0}"
    expect_out_lacks 'mismatch'
    expect_out_lacks 'syslog-missing'
    rm -f /var/mail/*
    end
  }
}

EXT_PARSE_MAIL=$'foo bar\nDefaults:ivan mailto=judy, mailsub="SUB %h %u"\n'
ext_parse_logged ext-parse-log-syntax-errors-mail-defaults \
  "$EXT_PARSE_MAIL"$'ivan ALL=(ALL) NOPASSWD: ALL\nbaz\n' 2 1
ext_parse_logged ext-parse-log-missing-include \
  $'@include /etc/66-ext-parse-missing\nfoo\n' 3 1
ext_parse_logged ext-parse-log-include-loop $'@include /etc/sudoers.d/66-ext-parse\n' 1 1
ext_parse_logged ext-parse-log-silent-error $'ivan ALL=(ALL) ALL : h=""\n' 2 1
ext_parse_logged ext-parse-log-duplicate-alias $'User_Alias A = ivan\nUser_Alias A = judy\n' 1 1
ext_parse_logged ext-parse-log-mailer-disabled $'Defaults mailerpath=/nonexistent\nfoo\n' 1 0

begin ext-parse-log-insecure-include && {
  printf 'ivan ALL=(ALL) NOPASSWD: ALL\n' >/etc/66-ext-parse-insecure
  chown ivan:root /etc/66-ext-parse-insecure
  chmod 0440 /etc/66-ext-parse-insecure
  ext_parse_policy $'@include /etc/66-ext-parse-insecure\n'
  ext_parse_log_script
  run root "python3 '$WORK/66-ext-parse-log.py'"
  rm -f /etc/66-ext-parse-insecure /var/mail/*
  expect_rc 0
  expect_out_line 'records=2 mails=1 logged=0'
  expect_out_has "is owned by uid $(id -u ivan), should be 0 ; PWD=/ ; USER=root ; "
  expect_out_lacks 'mismatch'
  expect_out_lacks 'syslog-missing'
  end
}

EXT_PARSE_LOGFILE_POLICY=$'Defaults logfile=/var/log/66-ext-parse.log, loglinelen=0\n'
ext_parse_logged ext-parse-log-invalid-default-logfile \
  "$EXT_PARSE_LOGFILE_POLICY"$'Defaults timestamp_timeout=bad\n' 1 1 1
ext_parse_logged ext-parse-log-invalid-default-facility \
  $'Defaults syslog=auth\nDefaults timestamp_timeout=bad\nivan ALL=(ALL) NOPASSWD: ALL\n' 1 1
ext_parse_logged ext-parse-log-unknown-default \
  $'Defaults 66_ext_parse_unknown\nivan ALL=(ALL) NOPASSWD: ALL\n' 1 1
ext_parse_logged ext-parse-log-cmnd-default-invalid \
  $'Defaults!/usr/bin/true timestamp_timeout=bad\nivan ALL=(ALL) NOPASSWD: ALL\n' 1 1
ext_parse_logged ext-parse-log-cmnd-default-unknown \
  $'Defaults!/usr/bin/true 66_ext_parse_unknown\nivan ALL=(ALL) NOPASSWD: ALL\n' 1 1
ext_parse_logged ext-parse-log-cmnd-default-logfile \
  "$EXT_PARSE_LOGFILE_POLICY"$'Defaults!/usr/bin/true timestamp_timeout=bad\n' 1 1 1
