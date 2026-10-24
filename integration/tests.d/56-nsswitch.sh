# sudo_nss.c compatibility: local files are consulted only when configured.
# Run reference-first. The explicit stricter branches below are intentional:
# lean-sudo cannot enforce remote policy and refuses the whole configuration,
# whereas sudo.ws may continue using files when the SSSD service is absent.

nsswitch_setup() {
  cp -a /etc/nsswitch.conf "$WORK/nsswitch.orig"
  sed '/^[[:blank:]]*[sS][uU][dD][oO][eE][rR][sS]:/d' \
    "$WORK/nsswitch.orig" >/etc/nsswitch.conf
  install -m 0440 /dev/stdin /etc/sudoers.d/nsswitch <<'EOF'
ivan ALL=(root) NOPASSWD: /usr/bin/id
EOF
}

nsswitch_restore() {
  cp -a "$WORK/nsswitch.orig" /etc/nsswitch.conf
}

nsswitch_expect_unsupported() {
  expect_rc 1
  expect_out_empty
  expect_err_has '/etc/nsswitch.conf: unsupported sudoers source:'
}

begin nsswitch-files && {
  nsswitch_setup
  printf '\n \tSuDoErS:\tFiLeS # local policy\n' >>/etc/nsswitch.conf
  run ivan 'sudo -n /usr/bin/id -u'
  expect_rc 0
  expect_out_line 0
  nsswitch_restore
  end
}

begin nsswitch-missing-entry && {
  nsswitch_setup
  run ivan 'sudo -n /usr/bin/id -u'
  expect_rc 0
  expect_out_line 0
  nsswitch_restore
  end
}

begin nsswitch-missing-file && {
  nsswitch_setup
  rm -f /etc/nsswitch.conf
  run ivan 'sudo -n /usr/bin/id -u'
  expect_rc 0
  expect_out_line 0
  nsswitch_restore
  end
}

begin nsswitch-files-actions && {
  nsswitch_setup
  printf '\nsudoers: files [SUCCESS=return] [NOTFOUND=return]\n' >>/etc/nsswitch.conf
  run ivan 'sudo -n /usr/bin/id -u'
  expect_rc 0
  expect_out_line 0
  nsswitch_restore
  end
}

begin nsswitch-files-continuation && {
  nsswitch_setup
  printf '\nsudoers: fi\\\n  les [NOTFOUND=return]\n' >>/etc/nsswitch.conf
  run ivan 'sudo -n /usr/bin/id -u'
  expect_rc 0
  expect_out_line 0
  nsswitch_restore
  end
}

begin nsswitch-first-entry && {
  nsswitch_setup
  printf '\nsudoers: files\nsudoers: sss\n' >>/etc/nsswitch.conf
  run ivan 'sudo -n /usr/bin/id -u'
  expect_rc 0
  expect_out_line 0
  nsswitch_restore
  end
}

begin nsswitch-sss-only && {
  nsswitch_setup
  printf '\nsudoers: sss\n' >>/etc/nsswitch.conf
  # The container has no SSSD service. Even though local policy grants this
  # command, neither implementation may fall back to that local grant.
  run ivan 'sudo -n /usr/bin/id -u'
  expect_rc 1
  expect_out_empty
  if [[ $LABEL != reference ]]; then nsswitch_expect_unsupported; fi
  nsswitch_restore
  end
}

begin nsswitch-mixed-files-sss && {
  nsswitch_setup
  printf '\nsudoers: files sss\n' >>/etc/nsswitch.conf
  run ivan 'sudo -n /usr/bin/id -u'
  if [[ $LABEL == reference ]]; then
    expect_rc 0
    expect_out_line 0
  else
    nsswitch_expect_unsupported
  fi
  nsswitch_restore
  end
}

begin nsswitch-return-does-not-hide-sss && {
  nsswitch_setup
  printf '\nsudoers: files [SUCCESS=return] sss\n' >>/etc/nsswitch.conf
  run ivan 'sudo -n /usr/bin/id -u'
  if [[ $LABEL == reference ]]; then
    expect_rc 0
    expect_out_line 0
  else
    nsswitch_expect_unsupported
  fi
  nsswitch_restore
  end
}

begin nsswitch-empty-entry && {
  nsswitch_setup
  printf '\nsudoers: # explicitly no sources\n' >>/etc/nsswitch.conf
  run ivan 'sudo -n /usr/bin/id -u'
  if [[ $LABEL == reference ]]; then
    # Upstream falls back to files if no recognized backend remains. The
    # replacement deliberately refuses an explicit entry without files.
    expect_rc 0
    expect_out_line 0
  else
    expect_rc 1
    expect_out_empty
    expect_err_has '/etc/nsswitch.conf: sudoers entry has no files source'
  fi
  nsswitch_restore
  end
}

begin nsswitch-unknown-source && {
  nsswitch_setup
  printf '\nsudoers: files unavailable_policy_backend\n' >>/etc/nsswitch.conf
  run ivan 'sudo -n /usr/bin/id -u'
  if [[ $LABEL == reference ]]; then
    expect_rc 0
    expect_out_line 0
  else
    nsswitch_expect_unsupported
  fi
  nsswitch_restore
  end
}

begin nsswitch-sss-never-loads-local-policy && {
  nsswitch_setup
  printf '\nsudoers: sss\n' >>/etc/nsswitch.conf
  # A refusal alone is insufficient: opening/parsing local policy first must
  # not leak a syntax diagnostic when files is absent from the source list.
  printf '\nNSS_LOCAL_POLICY_MUST_NOT_BE_READ !!!\n' >>/etc/sudoers
  run ivan 'sudo -n /usr/bin/id -u'
  expect_rc 1
  expect_out_empty
  expect_err_lacks 'syntax error'
  expect_err_lacks 'NSS_LOCAL_POLICY_MUST_NOT_BE_READ'
  if [[ $LABEL != reference ]]; then nsswitch_expect_unsupported; fi
  nsswitch_restore
  end
}
