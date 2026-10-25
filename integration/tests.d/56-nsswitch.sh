# sudo_nss.c compatibility: silently ignore backends absent from Ubuntu's build,
# and default to files only when no supported source remains. Unavailable SSSD
# is still a supported source and must never cause an implicit local fallback.

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
  nsswitch_restore
  end
}

begin nsswitch-mixed-files-sss && {
  nsswitch_setup
  printf '\nsudoers: files sss\n' >>/etc/nsswitch.conf
  run ivan 'sudo -n /usr/bin/id -u'
  expect_rc 0
  expect_out_line 0
  nsswitch_restore
  end
}

begin nsswitch-return-does-not-hide-sss && {
  nsswitch_setup
  printf '\nsudoers: files [SUCCESS=return] sss\n' >>/etc/nsswitch.conf
  run ivan 'sudo -n /usr/bin/id -u'
  expect_rc 0
  expect_out_line 0
  nsswitch_restore
  end
}

begin nsswitch-empty-entry && {
  nsswitch_setup
  printf '\nsudoers: # explicitly no sources\n' >>/etc/nsswitch.conf
  run ivan 'sudo -n /usr/bin/id -u'
  expect_rc 0
  expect_out_line 0
  [[ ! -s "$WORK/err" ]] || fail 'empty NSS source list emitted a warning'
  nsswitch_restore
  end
}

begin nsswitch-unknown-source && {
  nsswitch_setup
  printf '\nsudoers: files unavailable_policy_backend\n' >>/etc/nsswitch.conf
  run ivan 'sudo -n /usr/bin/id -u'
  expect_rc 0
  expect_out_line 0
  [[ ! -s "$WORK/err" ]] || fail 'ignored NSS source emitted a warning'
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
  nsswitch_restore
  end
}

for nsswitch_case in ldap mixed-ldap unknown-only ignored-only orphan-action unsupported-action malformed-action first-unsupported; do
  begin "nsswitch-$nsswitch_case" && {
    nsswitch_setup
    case $nsswitch_case in
      ldap) printf '\nsudoers: ldap\n' >>/etc/nsswitch.conf ;;
      mixed-ldap) printf '\nsudoers: ldap files LDAP\n' >>/etc/nsswitch.conf ;;
      unknown-only) printf '\nsudoers: unavailable_policy_backend\n' >>/etc/nsswitch.conf ;;
      ignored-only) printf '\nsudoers: ldap unavailable_policy_backend\n' >>/etc/nsswitch.conf ;;
      orphan-action) printf '\nsudoers: [SUCCESS=return]\n' >>/etc/nsswitch.conf ;;
      unsupported-action) printf '\nsudoers: files [UNAVAIL=return] [SUCCESS=continue]\n' >>/etc/nsswitch.conf ;;
      malformed-action) printf '\nsudoers: files [SUCCESS=return sss]\n' >>/etc/nsswitch.conf ;;
      first-unsupported) printf '\nsudoers: ldap\nsudoers: sss\n' >>/etc/nsswitch.conf ;;
    esac
    run ivan 'sudo -n /usr/bin/id -u'
    expect_rc 0
    expect_out_line 0
    [[ ! -s "$WORK/err" ]] || fail 'ignored NSS configuration emitted a warning'
    nsswitch_restore
    end
  }
done

begin nsswitch-ignored-sources-do-not-replace-sss && {
  nsswitch_setup
  printf '\nsudoers: ldap SSS unavailable_policy_backend\n' >>/etc/nsswitch.conf
  printf '\nNSS_LOCAL_POLICY_MUST_NOT_BE_READ !!!\n' >>/etc/sudoers
  run ivan 'sudo -n /usr/bin/id -u'
  expect_rc 1
  expect_out_empty
  expect_err_lacks 'unsupported'
  expect_err_lacks 'NSS_LOCAL_POLICY_MUST_NOT_BE_READ'
  nsswitch_restore
  end
}
