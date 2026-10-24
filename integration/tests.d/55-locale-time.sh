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
