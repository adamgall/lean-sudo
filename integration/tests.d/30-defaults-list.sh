# Compare listing stdout byte-for-byte with sudo.ws, including the final newline.
compare_list_reference() {
  local options=$1
  run root '/usr/sbin/visudo.ws -cq'
  expect_rc 0
  run root "sudo $options >'$WORK/actual-list'; actual=\$?; /usr/bin/sudo.ws $options >'$WORK/reference-list'; reference=\$?; test \"\$actual\" = 0 && test \"\$reference\" = 0 && diff -u '$WORK/reference-list' '$WORK/actual-list'"
  expect_rc 0
}

for list_user in alice dave erin frank carol; do
  begin "defaults-list-short-$list_user" && {
    compare_list_reference "-l -U $list_user"
    end
  }
  begin "defaults-list-long-$list_user" && {
    compare_list_reference "-ll -U $list_user"
    end
  }
done

begin defaults-list-command-short && {
  compare_list_reference '-l -U alice /usr/bin/id -u'
  end
}

begin defaults-list-command-long && {
  compare_list_reference '-ll -U alice /usr/bin/id -u'
  end
}

begin defaults-list-alias-negation-tags && {
  install -m 0440 /dev/stdin /etc/sudoers.d/zz-list <<'EOF'
Cmnd_Alias L_COMMANDS = /bin/sh, !/bin/bash
Runas_Alias L_USERS = root, !daemon
ivan ALL = (L_USERS : root) SETENV: NOPASSWD: ALL, !L_COMMANDS, (root) /bin/true, (root) /bin/false
EOF
  compare_list_reference '-l -U ivan'
  compare_list_reference '-ll -U ivan'
  end
}

begin defaults-list-myself-and-bound && {
  install -m 0440 /dev/stdin /etc/sudoers.d/zz-list <<'EOF'
Runas_Alias L_USERS = root, daemon
Cmnd_Alias L_COMMANDS = /bin/true, /bin/false
Defaults> L_USERS !set_logname
Defaults! L_COMMANDS umask=077
ivan ALL = () NOPASSWD: /bin/true, (:root) /usr/bin/id
EOF
  compare_list_reference '-l -U ivan'
  compare_list_reference '-ll -U ivan'
  end
}

begin defaults-unknown-warning && {
  install -m 0440 /dev/stdin /etc/sudoers.d/zz-defaults <<'EOF'
Defaults future_unknown_option
ivan ALL = NOPASSWD: /usr/bin/true
EOF
  run ivan 'sudo -n /usr/bin/true'
  expect_rc 0
  expect_err_has 'unknown defaults entry "future_unknown_option"'
  end
}

begin defaults-ignore-unknown-early && {
  install -m 0440 /dev/stdin /etc/sudoers.d/zz-defaults <<'EOF'
Defaults future_unknown_option
Defaults ignore_unknown_defaults
ivan ALL = NOPASSWD: /usr/bin/true
EOF
  run ivan 'sudo -n /usr/bin/true'
  expect_rc 0
  expect_err_lacks 'unknown defaults entry'
  end
}

begin defaults-compiled-environment && {
  install -m 0440 /dev/stdin /etc/sudoers.d/zz-defaults <<'EOF'
ivan ALL = NOPASSWD: /usr/bin/printenv
EOF
  XENV=(DPKG_COLORS=always)
  run ivan 'sudo -n /usr/bin/printenv DPKG_COLORS'
  expect_rc 0
  expect_out_line always
  end
}

begin defaults-scoping-file-order && {
  install -m 0440 /dev/stdin /etc/sudoers.d/zz-defaults <<'EOF'
Defaults:ivan env_keep += "TEST_SCOPE"
Defaults env_keep -= "TEST_SCOPE"
ivan ALL = NOPASSWD: /usr/bin/printenv
EOF
  XENV=(TEST_SCOPE=must-not-survive)
  run ivan 'sudo -n /usr/bin/printenv TEST_SCOPE'
  expect_rc 1
  expect_out_empty
  end
}

begin defaults-list-quoting-digests && {
  install -m 0440 /dev/stdin /etc/sudoers.d/zz-list <<'EOF'
Defaults:ivan passprompt="tab test", env_keep += "VAR\\NAME"
ivan ALL = (ALL, !%root, "%space group") NOPASSWD: /tmp/a\ b foo\#bar, sha256:AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA= !/bin/true
EOF
  compare_list_reference '-l -U ivan'
  compare_list_reference '-ll -U ivan'
  end
}

begin defaults-list-options-time && {
  install -m 0440 /dev/stdin /etc/sudoers.d/zz-list <<'EOF'
ivan ALL = (root) CWD=/tmp TIMEOUT=2m NOTBEFORE=20240101000000Z NOTAFTER=20300101000000Z NOPASSWD: /bin/true, CWD=/tmp /bin/false
EOF
  compare_list_reference '-l -U ivan'
  compare_list_reference '-ll -U ivan'
  end
}
