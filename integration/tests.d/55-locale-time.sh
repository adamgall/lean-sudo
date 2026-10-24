# Ubuntu resolute sudo.ws 1.9.17p2 source-backed regressions; run reference first.
# TZ: debian/patches/CVE-2026-96512.patch (unsetenv + tzset, retain submit env).
# Messages: src/sudo.c setlocale; plugins/sudoers/auth/pam.c PAM_PROMPT_IS_PASSWORD.
# Matching: plugins/sudoers/sudoers.c sudoers_lookup under SUDOERS_LOCALE_SUDOERS,
# plugins/sudoers/locale.c configured locale with C fallback.
# Source tree: https://git.launchpad.net/ubuntu/+source/sudo/tree/?h=ubuntu/resolute-updates

# Unlike the later 80-i18n helper, this deliberately exercises sudo.ws first.
locale_time_compare_reference() {
  local user=$1 command=$2 status=$3
  run "$user" 'sudo() { /bin/bash -c '\''exec -a sudo /usr/bin/sudo.ws "$@"'\'' -- "$@"; }; '"$command"
  expect_rc "$status"
  cp "$WORK/out" "$WORK/locale-reference-out"
  cp "$WORK/err" "$WORK/locale-reference-err"
  run "$user" "$command"
  expect_rc "$status"
  diff -u "$WORK/locale-reference-out" "$WORK/out" >>"$LOG" || fail 'stdout differs from sudo.ws'
  diff -u "$WORK/locale-reference-err" "$WORK/err" >>"$LOG" || fail 'stderr differs from sudo.ws'
}

begin locale-time-TZ-notafter-bypass && {
  # No Z suffix: this is a system-local civil time, not an absolute UTC time.
  # A caller-selected zone 12 hours behind UTC used to resurrect this rule.
  expired=$(env -u TZ date -d '1 hour ago' +%Y%m%d%H%M%S)
  printf 'ivan ALL = NOTAFTER=%s NOPASSWD: /usr/bin/id\n' "$expired" >/etc/sudoers.d/locale-time
  chmod 0440 /etc/sudoers.d/locale-time
  XENV=(TZ=UTC+12)
  locale_time_compare_reference ivan 'sudo -n /usr/bin/id -u' 1
  expect_out_empty
  end
}

begin locale-time-TZ-notbefore-bypass && {
  future=$(env -u TZ date -d '+1 hour' +%Y%m%d%H%M%S)
  printf 'ivan ALL = NOTBEFORE=%s NOPASSWD: /usr/bin/id\n' "$future" >/etc/sudoers.d/locale-time
  chmod 0440 /etc/sudoers.d/locale-time
  XENV=(TZ=UTC-12)
  locale_time_compare_reference ivan 'sudo -n /usr/bin/id -u' 1
  expect_out_empty
  end
}

begin locale-time-TZ-command-environment-preserved && {
  # Sanitizing sudo's own clock must not discard an allowed command variable.
  install -m 0440 /dev/stdin /etc/sudoers.d/locale-time <<'EOF'
Defaults:ivan env_keep += "TZ"
ivan ALL = NOPASSWD: /usr/bin/printenv TZ
EOF
  XENV=(TZ=UTC+12)
  locale_time_compare_reference ivan 'sudo -n /usr/bin/printenv TZ' 0
  expect_out_line UTC+12
  end
}

begin locale-time-de-PAM-generic-prompt && {
  # A literal generic sudo prompt yields to Linux-PAM's translated prompt.
  # Assert the translation is actually installed, so English fallback cannot
  # accidentally pass the translated-prompt recognition regression below.
  install -m 0440 /dev/stdin /etc/sudoers.d/locale-time <<'EOF'
Defaults:alice lecture=never,passprompt="Password: ",!passprompt_override
EOF
  XENV=(LANG=de_DE.UTF-8)
  locale_time_compare_reference alice "printf 'alicepw\n' | sudo -kS /usr/bin/true" 0
  expect_err_has 'Passwort'
  expect_err_lacks 'Password:'
  end
}

begin locale-time-de-PAM-generic-prompt-replaced && {
  # A translated generic PAM prompt must be replaced even without override.
  install -m 0440 /dev/stdin /etc/sudoers.d/locale-time <<'EOF'
Defaults:alice lecture=never,passprompt="Locale password for %p: ",!passprompt_override
EOF
  XENV=(LANG=de_DE.UTF-8)
  locale_time_compare_reference alice "printf 'alicepw\n' | sudo -kS /usr/bin/true" 0
  [[ $ERR == 'Locale password for alice: ' ]] || fail 'Translated generic PAM prompt was not replaced'
  end
}

begin locale-time-de-libc-missing-home && {
  oldhome=$(getent passwd ivan | cut -d: -f6)
  usermod -d /nonexistent-lean-sudo-locale-home ivan
  XENV=(LANG=de_DE.UTF-8)
  # Pin libc's localized strerror separately from the diagnostic's translated
  # format string: this test targets C locale activation, not catalog rendering.
  run root '/bin/bash -c '\''exec -a sudo /usr/bin/sudo.ws -n -i -u ivan /bin/echo login-continued'\'''
  expect_rc 0
  locale_reference_error=${ERR##*: }
  [[ $locale_reference_error != 'No such file or directory' && -n $locale_reference_error ]] || fail 'Reference libc message did not localize'
  run root 'sudo -n -i -u ivan /bin/echo login-continued'
  usermod -d "$oldhome" ivan
  expect_rc 0
  expect_out_line login-continued
  [[ ${ERR##*: } == "$locale_reference_error" ]] || fail 'libc strerror differs from sudo.ws'
  end
}

begin locale-time-regex-caller-locale-independent && {
  install -m 0440 /dev/stdin /etc/sudoers.d/locale-time <<'EOF'
ivan ALL = NOPASSWD: /usr/bin/echo ^.$
EOF
  XENV=(LANG=de_DE.UTF-8 LC_ALL=de_DE.UTF-8)
  # In C a dot matches a byte, not the two-byte UTF-8 character é.
  locale_time_compare_reference ivan 'sudo -n /usr/bin/echo é' 1
  expect_out_empty
  locale_time_compare_reference ivan 'sudo -n /usr/bin/echo a' 0
  expect_out_line a
  end
}

begin locale-time-regex-sudoers-locale && {
  install -m 0440 /dev/stdin /etc/sudoers.d/locale-time <<'EOF'
Defaults sudoers_locale=de_DE.UTF-8
ivan ALL = NOPASSWD: /usr/bin/echo ^.$
EOF
  XENV=(LANG=C)
  # Only the administrator-selected policy locale may change matching.
  locale_time_compare_reference ivan 'sudo -n /usr/bin/echo é' 0
  expect_out_line é
  end
}

locale_time_logging() {
  local policy_locale=$1 caller_locale=$2
  rm -rf /var/log/locale-time-io /var/log/locale-time.log
  install -m 0440 /dev/stdin /etc/sudoers.d/locale-time <<EOF
Defaults:judy sudoers_locale=$policy_locale,log_output,iolog_dir=/var/log/locale-time-io,iolog_file="%{user}/%x",logfile=/var/log/locale-time.log
judy ALL=(root) NOPASSWD: /usr/bin/true
EOF
  XENV=(LC_ALL="$caller_locale")
  run judy 'sudo -n /usr/bin/true'
  expect_rc 0
  local expected_date expected_month
  # Python uses libc strftime; Rust date's %x differs from libc's German format.
  expected_date=$(python3 -c 'import locale,sys,time; locale.setlocale(locale.LC_ALL,sys.argv[1]); print(time.strftime("%x"))' "$policy_locale")
  expected_month=$(python3 -c 'import locale,sys,time; locale.setlocale(locale.LC_ALL,sys.argv[1]); print(time.strftime("%b %e "))' "$policy_locale")
  if [[ ! -f "/var/log/locale-time-io/judy/$expected_date/log" ]]; then
    find /var/log/locale-time-io -type f
    fail "I/O log path does not use the expected locale date $expected_date"
  fi
  grep -qF "$expected_month" /var/log/locale-time.log ||
    fail "logfile timestamp does not use sudoers_locale $policy_locale"
}

begin locale-time-logging-default-C && {
  locale_time_logging C de_DE.UTF-8
  end
}

begin locale-time-logging-configured-de && {
  locale_time_logging de_DE.UTF-8 C
  end
}

begin locale-time-json-timestamps-default-C && {
  rm -f /var/log/locale-time.json
  install -m 0440 /dev/stdin /etc/sudoers.d/locale-time <<'EOF'
Defaults:judy log_format=json_compact,logfile=/var/log/locale-time.json
judy ALL=(root) NOPASSWD: /usr/bin/true
EOF
  XENV=(LC_ALL=de_DE.UTF-8)
  run judy 'sudo -n /usr/bin/true'
  expect_rc 0
  python3 - <<'PY' || fail 'JSON localtime is not in the sudoers C locale'
import json, locale, time
locale.setlocale(locale.LC_TIME, "C")
count = 0
def check(value):
    global count
    if isinstance(value, dict):
        if "localtime" in value:
            assert value["localtime"] == time.strftime("%b %e %H:%M:%S", time.localtime(value["seconds"])), value
            count += 1
        for child in value.values():
            check(child)
    elif isinstance(value, list):
        for child in value:
            check(child)
for line in open("/var/log/locale-time.json"):
    check(json.loads(line))
assert count >= 2, count
PY
  end
}
