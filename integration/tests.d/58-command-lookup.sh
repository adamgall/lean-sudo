



command_lookup_fixture() {
  lookup="$WORK/command-lookup"
  install -d -o root -g root -m 0755 "$lookup" "$lookup/public"
  install -d -o root -g root -m 0700 "$lookup/root"
  install -d -o alice -g "$(gid_of alice)" -m 0700 "$lookup/alice"
  install -d -o bob -g "$(gid_of bob)" -m 0700 "$lookup/bob"
  printf '#!/bin/sh\nprintf "root-only\\n"\n' >"$lookup/public/admin-only"
  chmod 0700 "$lookup/public/admin-only"
  install -o root -g root -m 0700 "$lookup/public/admin-only" "$lookup/root/admin-private"
  printf '#!/bin/sh\nprintf "invoker-candidate\\n"\n' >"$lookup/alice/lookup-choice"
  chown alice:"$(gid_of alice)" "$lookup/alice/lookup-choice"
  chmod 0755 "$lookup/alice/lookup-choice"
  printf '#!/bin/sh\nprintf "runas-candidate\\n"\n' >"$lookup/bob/lookup-choice"
  chown bob:"$(gid_of bob)" "$lookup/bob/lookup-choice"
  chmod 0700 "$lookup/bob/lookup-choice"
  install -m 0440 /dev/stdin /etc/sudoers.d/command-lookup <<EOF
Defaults:alice secure_path="$lookup/public:$lookup/root:/usr/bin:/bin"
alice ALL=(ALL) NOPASSWD: ALL
EOF
}

begin command-lookup-root-0700-absolute && {
  command_lookup_fixture
  run alice "sudo -n '$lookup/public/admin-only'"
  expect_rc 0
  expect_out_line root-only
  end
}

begin command-lookup-root-0700-bare && {
  command_lookup_fixture
  run alice 'sudo -n admin-only'
  expect_rc 0
  expect_out_line root-only
  end
}

begin command-lookup-root-0700-list && {
  command_lookup_fixture
  run alice 'sudo -n -l admin-only'
  expect_rc 0
  expect_out_line "$lookup/public/admin-only"
  run alice "sudo -n -l '$lookup/public/admin-only'"
  expect_rc 0
  expect_out_line "$lookup/public/admin-only"
  end
}

begin command-lookup-private-root-directory && {
  command_lookup_fixture
  run alice "sudo -n '$lookup/root/admin-private'"
  expect_rc 0
  expect_out_line root-only
  run alice 'sudo -n admin-private'
  expect_rc 0
  expect_out_line root-only
  run alice 'sudo -n -l admin-private'
  expect_rc 0
  expect_out_line "$lookup/root/admin-private"
  end
}

begin command-lookup-runas-before-invoker && {
  command_lookup_fixture
  printf 'Defaults:alice secure_path="%s/alice:%s/bob:/usr/bin:/bin"\n' "$lookup" "$lookup" >>/etc/sudoers.d/command-lookup
  run alice 'sudo -n -u bob lookup-choice'
  expect_rc 0
  expect_out_line runas-candidate
  run alice 'sudo -n -u bob -l lookup-choice'
  expect_rc 0
  expect_out_line "$lookup/bob/lookup-choice"
  end
}

begin command-lookup-invoker-private-fallback-list && {
  command_lookup_fixture
  printf 'Defaults:alice secure_path="%s/alice:/usr/bin:/bin"\n' "$lookup" >>/etc/sudoers.d/command-lookup
  run alice 'sudo -n -u bob -l lookup-choice'
  expect_rc 0
  expect_out_line "$lookup/alice/lookup-choice"
  run alice "sudo -n -u bob -l '$lookup/alice/lookup-choice'"
  expect_rc 0
  expect_out_line "$lookup/alice/lookup-choice"
  end
}

begin command-lookup-invoker-fallback-not-exec-permission && {
  command_lookup_fixture
  printf 'Defaults:alice secure_path="%s/alice:/usr/bin:/bin"\n' "$lookup" >>/etc/sudoers.d/command-lookup


  run alice 'sudo -n -u bob lookup-choice'
  expect_rc 1
  expect_out_empty
  expect_err_has 'Permission denied'
  expect_err_lacks 'command not found'
  end
}

begin command-lookup-any-execute-bit && {
  command_lookup_fixture
  for mode in 0100 0010 0001; do
    install -o root -g root -m "$mode" "$lookup/public/admin-only" "$lookup/public/any-x"
    run alice "sudo -n -u bob -l '$lookup/public/any-x'"
    expect_rc 0
    expect_out_line "$lookup/public/any-x"
  done
  end
}

begin command-lookup-reject-nonexecutables && {
  command_lookup_fixture
  install -o root -g root -m 0644 "$lookup/public/admin-only" "$lookup/public/no-x"
  install -d -o root -g root -m 0755 "$lookup/public/not-regular"
  for name in no-x not-regular absent; do
    run alice "sudo -n '$lookup/public/$name'"
    expect_rc 1
    expect_err_has 'command not found'
  done
  end
}

begin command-lookup-dot-does-not-fallback && {
  command_lookup_fixture
  install -o root -g root -m 0755 "$lookup/public/admin-only" "$lookup/public/lookup-choice"
  printf 'Defaults:alice secure_path="%s/alice:.:/usr/bin:/bin",ignore_dot\n' "$lookup" >>/etc/sudoers.d/command-lookup


  run alice "cd '$lookup/public' && sudo -n -u bob lookup-choice"
  expect_rc 1
  expect_out_empty
  expect_err_has 'ignoring "lookup-choice" found in '\''.'\'''
  expect_err_has 'Use "sudo ./lookup-choice"'
  end
}

unset -f command_lookup_fixture
