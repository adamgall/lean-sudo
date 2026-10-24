# sudo.ws match.c / match_command.c regressions.
begin policy-myself-empty-runas && {
  printf 'ivan ALL = () NOPASSWD: /usr/bin/id\n' >/etc/sudoers.d/policy
  chmod 0440 /etc/sudoers.d/policy
  run ivan 'sudo -n /usr/bin/id -u'; expect_rc 1; expect_out_empty
  run ivan 'sudo -n -u ivan /usr/bin/id -u'; expect_rc 0; expect_out_line "$(uid_of ivan)"
  end
}
begin policy-myself-empty-colon && {
  printf 'ivan ALL = (:) NOPASSWD: /usr/bin/id\n' >/etc/sudoers.d/policy
  chmod 0440 /etc/sudoers.d/policy
  run ivan 'sudo -n /usr/bin/id -u'; expect_rc 1; expect_out_empty
  end
}
begin policy-glob-negation-usrmerge && {
  printf 'ivan ALL = (ALL) NOPASSWD: ALL, !/usr/bin/i[d]\n' >/etc/sudoers.d/policy
  chmod 0440 /etc/sudoers.d/policy
  run ivan 'sudo -n /bin/id -u'; expect_rc 1; expect_out_empty
  run ivan 'cd /usr/bin; sudo -n ./id -u'; expect_rc 1; expect_out_empty
  end
}
begin policy-glob-positive-usrmerge && {
  printf 'ivan ALL = NOPASSWD: /usr/bin/i[d]\n' >/etc/sudoers.d/policy
  chmod 0440 /etc/sudoers.d/policy
  run ivan 'sudo -n /bin/id -u'; expect_rc 0; expect_out_line 0
  end
}
begin policy-fast-glob-canonical-parent && {
  printf 'Defaults:ivan fast_glob\nivan ALL = NOPASSWD: /usr/bin/i[d]\n' >/etc/sudoers.d/policy
  chmod 0440 /etc/sudoers.d/policy
  run ivan 'sudo -n /bin/id -u'; expect_rc 0; expect_out_line 0
  end
}
begin policy-literal-symlink-parent && {
  printf 'ivan ALL = NOPASSWD: /usr/bin/id\n' >/etc/sudoers.d/policy
  chmod 0440 /etc/sudoers.d/policy
  run ivan 'mkdir -p "$HOME/policy-bin"; ln -sf /usr/bin/id "$HOME/policy-bin/id"; sudo -n "$HOME/policy-bin/id" -u'
  expect_rc 1; expect_out_empty
  run ivan 'sudo -n /bin/id -u'; expect_rc 0; expect_out_line 0
  end
}
begin policy-directory-symlink-parent && {
  printf 'ivan ALL = NOPASSWD: /usr/bin/\n' >/etc/sudoers.d/policy
  chmod 0440 /etc/sudoers.d/policy
  run ivan 'mkdir -p "$HOME/policy-bin"; ln -sf /usr/bin/id "$HOME/policy-bin/id"; sudo -n "$HOME/policy-bin/id" -u'
  expect_rc 1; expect_out_empty
  run ivan 'sudo -n /bin/id -u'; expect_rc 0; expect_out_line 0
  end
}
begin policy-fqdn-negated-host && {
  cp /etc/hosts "$WORK/policy-hosts"
  { printf '127.0.1.1 %s.example.test %s\n' "$host" "$host"; cat "$WORK/policy-hosts"; } >/etc/hosts
  printf 'ivan ALL, !%s.example.test = NOPASSWD: /usr/bin/id\n' "$host" >/etc/sudoers.d/policy
  chmod 0440 /etc/sudoers.d/policy
  run ivan 'sudo -n /usr/bin/id -u'; expect_rc 1; expect_out_empty
  cat "$WORK/policy-hosts" >/etc/hosts
  end
}
begin policy-case-insensitive-user-denial && {
  printf 'ALL, !IvAn ALL = NOPASSWD: /usr/bin/id\n' >/etc/sudoers.d/policy
  chmod 0440 /etc/sudoers.d/policy
  run ivan 'sudo -n /usr/bin/id -u'; expect_rc 1; expect_out_empty
  end
}
begin policy-case-insensitive-runas-denial && {
  printf 'ivan ALL = (ALL, !RoOt) NOPASSWD: /usr/bin/id\n' >/etc/sudoers.d/policy
  chmod 0440 /etc/sudoers.d/policy
  run ivan 'sudo -n /usr/bin/id -u'; expect_rc 1; expect_out_empty
  end
}
begin policy-case-insensitive-group && {
  printf '%%IvAn ALL = NOPASSWD: /usr/bin/id\n' >/etc/sudoers.d/policy
  chmod 0440 /etc/sudoers.d/policy
  run ivan 'sudo -n /usr/bin/id -u'; expect_rc 0; expect_out_line 0
  end
}
begin policy-case-sensitive-optout && {
  printf 'Defaults !case_insensitive_user\nALL, !IvAn ALL = NOPASSWD: /usr/bin/id\n' >/etc/sudoers.d/policy
  chmod 0440 /etc/sudoers.d/policy
  run ivan 'sudo -n /usr/bin/id -u'; expect_rc 0; expect_out_line 0
  end
}
begin policy-hex-name-negation && {
  printf '%s\n' 'ivan ALL = NOPASSWD: ALL' '\x69van ALL = !/usr/bin/id' >/etc/sudoers.d/policy
  chmod 0440 /etc/sudoers.d/policy
  run ivan 'sudo -n /usr/bin/id -u'; expect_rc 1; expect_out_empty
  end
}
begin policy-indented-hash-include-comment && {
  printf 'ivan ALL = NOPASSWD: /usr/bin/id\n' >"$WORK/policy-extra"
  chmod 0440 "$WORK/policy-extra"
  printf '  #include %s/policy-extra\n' "$WORK" >/etc/sudoers.d/policy
  chmod 0440 /etc/sudoers.d/policy
  run ivan 'sudo -n /usr/bin/id -u'; expect_rc 1; expect_out_empty
  end
}
begin policy-command-and-argument-regex && {
  printf 'ivan ALL = NOPASSWD: ^/usr/bin/i[d]$ ^-u$\n' >/etc/sudoers.d/policy
  chmod 0440 /etc/sudoers.d/policy
  run ivan 'sudo -n /bin/id -u'; expect_rc 0; expect_out_line 0
  run ivan 'sudo -n /bin/id -g'; expect_rc 1; expect_out_empty
  end
}
begin policy-command-digest && {
  digest=$(sha256sum /usr/bin/dash); digest=${digest%% *}
  printf 'ivan ALL = NOPASSWD: sha256:%s /usr/bin/dash\n' "$digest" >/etc/sudoers.d/policy
  chmod 0440 /etc/sudoers.d/policy
  run ivan "sudo -n /usr/bin/dash -c 'echo digest-ok'"; expect_rc 0; expect_out_line digest-ok
  printf 'Cmnd_Alias VERIFIED = sha256:%s /usr/bin/dash\nivan ALL = NOPASSWD: VERIFIED\n' "$digest" >/etc/sudoers.d/policy
  run ivan "sudo -n /usr/bin/dash -c 'echo digest-alias-ok'"; expect_rc 0; expect_out_line digest-alias-ok
  printf 'ivan ALL = NOPASSWD: sha256:%064d /usr/bin/dash\n' 0 >/etc/sudoers.d/policy
  run ivan "sudo -n /usr/bin/dash -c 'echo digest-ok'"; expect_rc 1; expect_out_empty
  end
}
begin policy-validity-window && {
  printf 'ivan ALL = NOTBEFORE=20990101000000Z NOPASSWD: /usr/bin/id\n' >/etc/sudoers.d/policy
  chmod 0440 /etc/sudoers.d/policy
  run ivan 'sudo -n /usr/bin/id -u'; expect_rc 1; expect_out_empty
  printf 'ivan ALL = NOTAFTER=20000101000000Z NOPASSWD: /usr/bin/id\n' >/etc/sudoers.d/policy
  run ivan 'sudo -n /usr/bin/id -u'; expect_rc 1; expect_out_empty
  end
}
begin policy-list-pseudo-command && {
  printf 'ivan ALL = (judy) NOPASSWD: list\njudy ALL = NOPASSWD: /usr/bin/id\n' >/etc/sudoers.d/policy
  chmod 0440 /etc/sudoers.d/policy
  run ivan 'sudo -n -l -U judy'; expect_rc 0; expect_out_has '/usr/bin/id'
  run ivan 'sudo -n -l -U kate'; expect_rc 1
  # sudo accepts but deliberately ignores file digests on pseudo-commands.
  printf 'ivan ALL = (judy) NOPASSWD: sha256:%064d list\njudy ALL = NOPASSWD: /usr/bin/id\n' 0 >/etc/sudoers.d/policy
  run ivan 'sudo -n -l -U judy'; expect_rc 0; expect_out_has '/usr/bin/id'
  end
}
begin policy-preserve-groups-runas-fallback && {
  printf 'Defaults:ivan preserve_groups\nivan ALL = (root) NOPASSWD: /usr/bin/id\n' >/etc/sudoers.d/policy
  chmod 0440 /etc/sudoers.d/policy
  run ivan 'sudo -n -u root -g ivan /usr/bin/id -g'; expect_rc 0; expect_out_line "$(gid_of ivan)"
  end
}
begin policy-nonunix-group-no-plugin && {
  printf '%%:ivan ALL = NOPASSWD: /usr/bin/id\n' >/etc/sudoers.d/policy
  chmod 0440 /etc/sudoers.d/policy
  run ivan 'sudo -n /usr/bin/id -u'; expect_rc 1; expect_out_empty
  end
}
begin policy-interface-network && {
  printf 'ivan 127.0.0.0/8 = NOPASSWD: /usr/bin/id\n' >/etc/sudoers.d/policy
  chmod 0440 /etc/sudoers.d/policy
  # sudo excludes the loopback interface; --network none has no eligible NIC.
  run ivan 'sudo -n /usr/bin/id -u'; expect_rc 1; expect_out_empty
  end
}
begin policy-netgroup-user-and-host && {
  cp /etc/nsswitch.conf "$WORK/policy-nsswitch"
  printf 'passwd: files\ngroup: files\nshadow: files\nhosts: files dns\nnetgroup: files\n' >/etc/nsswitch.conf
  printf 'policyusers (,ivan,)\npolicyhosts (%s,,)\n' "$host" >/etc/netgroup
  printf '+policyusers +policyhosts = NOPASSWD: /usr/bin/id\n' >/etc/sudoers.d/policy
  chmod 0440 /etc/sudoers.d/policy
  run ivan 'sudo -n /usr/bin/id -u'; expect_rc 0; expect_out_line 0
  printf 'Defaults !use_netgroups\n+policyusers ALL = NOPASSWD: /usr/bin/id\n' >/etc/sudoers.d/policy
  run ivan 'sudo -n /usr/bin/id -u'; expect_rc 1; expect_out_empty
  cat "$WORK/policy-nsswitch" >/etc/nsswitch.conf
  rm -f /etc/netgroup
  end
}
begin policy-negated-only-list-and-validate && {
  printf 'ivan ALL = NOPASSWD: !ALL\n' >/etc/sudoers.d/policy
  chmod 0440 /etc/sudoers.d/policy
  run ivan 'sudo -n -l'; expect_rc 0; expect_out_has '!ALL'
  run ivan 'sudo -n -v'; expect_rc 0
  run ivan 'sudo -n /usr/bin/id -u'; expect_rc 1; expect_out_empty
  end
}
