ext_plugins_setup() {
  EXT_PLUGINS_IO=/var/tmp/ext-plugins-io
  rm -rf "$EXT_PLUGINS_IO" "$WORK/ext-plugins-sudo.conf"
  if [[ -e /etc/sudo.conf ]]; then cp -a /etc/sudo.conf "$WORK/ext-plugins-sudo.conf"; fi
  printf '%s\n' "$@" >/etc/sudo.conf
  chmod 0644 /etc/sudo.conf
  printf 'Defaults:ivan !lecture, log_output, iolog_dir=%s\nivan ALL=(ALL) NOPASSWD: ALL\n' \
    "$EXT_PLUGINS_IO" >/etc/sudoers.d/66-ext-plugins
  chmod 0440 /etc/sudoers.d/66-ext-plugins
}

ext_plugins_cleanup() {
  if [[ -e $WORK/ext-plugins-sudo.conf ]]; then
    cp -a "$WORK/ext-plugins-sudo.conf" /etc/sudo.conf
  else
    rm -f /etc/sudo.conf
  fi
  rm -rf "$EXT_PLUGINS_IO" "$WORK/ext-plugins-sudo.conf" /etc/sudoers.d/66-ext-plugins
}

ext_plugins_state() {
  find "$EXT_PLUGINS_IO" -mindepth 1 -printf '%P %y\n' 2>/dev/null | sort
}

ext_plugins_sessions() {
  local count
  count=$(find "$EXT_PLUGINS_IO" -name log.json | wc -l)
  [[ $count == 1 ]] || fail "expected one I/O log session: [$(ext_plugins_state)]"
}

begin ext-plugins-policy-only-sudo-conf-no-iolog && {
  ext_plugins_setup 'Plugin sudoers_policy sudoers.so'
  run ivan 'sudo -n /bin/echo ext-plugins-output'
  expect_rc 0
  expect_out_line ext-plugins-output
  state=$(ext_plugins_state)
  [[ $state == 'seq f' ]] || fail "I/O log state: expected only the sequence file, got [$state]"
  [[ $(cat "$EXT_PLUGINS_IO/seq" 2>/dev/null) == 000001 ]] || fail 'sequence number not allocated'
  ext_plugins_cleanup
  end
}

begin ext-plugins-policy-and-sudoers-io-logs-session && {
  ext_plugins_setup 'Plugin sudoers_policy sudoers.so' 'Plugin sudoers_io sudoers.so'
  run ivan 'sudo -n /bin/echo ext-plugins-output'
  expect_rc 0
  expect_out_line ext-plugins-output
  ext_plugins_sessions
  [[ -f $EXT_PLUGINS_IO/00/00/01/log.json ]] || fail "no session 000001: [$(ext_plugins_state)]"
  ext_plugins_cleanup
  end
}

begin ext-plugins-sudoers-io-with-options-single-session && {
  ext_plugins_setup 'Plugin sudoers_policy sudoers.so' \
    'Plugin sudoers_io sudoers.so iolog_flush=true'
  run ivan 'sudo -n /bin/echo ext-plugins-output'
  expect_rc 0
  expect_out_line ext-plugins-output
  ext_plugins_sessions
  [[ $(cat "$EXT_PLUGINS_IO/seq" 2>/dev/null) == 000001 ]] ||
    fail "sequence advanced more than once: [$(ext_plugins_state)]"
  ext_plugins_cleanup
  end
}
