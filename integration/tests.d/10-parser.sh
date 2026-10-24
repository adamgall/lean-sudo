# sudoers grammar and include semantics, exercised against both implementations.
begin parser-extended-grammar && {
  install -m 0440 /dev/stdin /etc/sudoers.d/parser <<'EOF'
User_Alias PARSER_USERS = +missingnetgroup, %:external, %:#1234, nick
Runas_Alias PARSER_RUNAS = +missingnetgroup, root
Host_Alias PARSER_HOSTS = 127.0.0.1, 10.0.0.0/8, 10.0.0.0/255.0.0.0, ::1, 2001:db8::/32, 2001:db8::/ffff:ffff::, 10.0.0.*, +missingnetgroup
nick ALL = () /usr/bin/true, (:) /usr/bin/false, (: root) /usr/bin/id
nick ALL = CWD=~ CHROOT=* TIMEOUT=1h2m3s NOTBEFORE=20260101000000Z NOTAFTER=20990101000000Z ROLE=sysadm_r TYPE=sysadm_t APPARMOR_PROFILE=test PRIVS=proc_exec LIMITPRIVS=proc_exec NOEXEC: INTERCEPT: LOG_INPUT: LOG_OUTPUT: MAIL: FOLLOW: SETENV: NOPASSWD: /usr/bin/true, EXEC: NOINTERCEPT: NOLOG_INPUT: NOLOG_OUTPUT: NOMAIL: NOFOLLOW: NOSETENV: PASSWD: /usr/bin/false
nick ALL = ^/usr/bin/(true|false)$ ^arg[:,]value$, list, /usr/bin/sudoedit /tmp/parser-edit
Defaults:nick passprompt=abc!def
Defaults@127.0.0.1 !lecture
Defaults>root !lecture
Defaults!/usr/bin/true !lecture
ivan ALL = NOPASSWD: /usr/bin/true
EOF
  for alg in 224 256 384 512; do
    digest=$(printf x | sha${alg}sum | cut -d' ' -f1)
    printf 'nick ALL = sha%s:%s /usr/bin/false\n' "$alg" "$digest" >>/etc/sudoers.d/parser
  done
  digest=$(printf x | sha256sum | cut -d' ' -f1)
  printf 'nick ALL = sha256:%s, sha256:AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA= /usr/bin/false\n' "$digest" >>/etc/sudoers.d/parser
  printf 'nick ALL = sha256:%s !/usr/bin/false, sha256:%s sudoedit /tmp/parser-edit, sha256:%s list\n' "$digest" "$digest" "$digest" >>/etc/sudoers.d/parser
  /usr/sbin/visudo.ws -cf /etc/sudoers.d/parser >"$WORK/check" 2>&1 || fail "reference visudo rejected extended grammar"
  run ivan 'sudo -n /usr/bin/true'
  expect_rc 0
  expect_err_lacks 'syntax error'
  end
}

begin parser-myself-does-not-grant-root && {
  install -m 0440 /dev/stdin /etc/sudoers.d/parser <<'EOF'
ivan ALL = () NOPASSWD: /usr/bin/id
judy ALL = (:) NOPASSWD: /usr/bin/id
EOF
  run ivan 'sudo -n /usr/bin/id -u'
  expect_rc 1
  run ivan 'sudo -n -u ivan /usr/bin/id -u'
  expect_rc 0
  expect_out_line "$(uid_of ivan)"
  run judy 'sudo -n /usr/bin/id -u'
  expect_rc 1
  end
}

begin parser-hex-word-escapes && {
  install -m 0440 /dev/stdin /etc/sudoers.d/parser <<'EOF'
\x69van ALL = NOPASSWD: /usr/bin/id
Defaults:ivan passprompt="\x50assword: "
EOF
  run ivan 'sudo -n /usr/bin/id -u'
  expect_rc 0
  expect_out_line 0
  end
}

begin parser-indented-hash-include-is-comment && {
  install -m 0440 /dev/stdin /etc/sudoers.d/parser <<'EOF'
  #include /nonexistent/parser-file
  @include /etc/parser-include
EOF
  install -m 0440 /dev/stdin /etc/parser-include <<'EOF'
ivan ALL = NOPASSWD: /usr/bin/true
EOF
  run ivan 'sudo -n /usr/bin/true'
  expect_rc 0
  end
}

begin parser-includedir-symlinks-and-nonregular && {
  install -m 0440 /dev/stdin /etc/parser-target <<'EOF'
ivan ALL = NOPASSWD: /usr/bin/true
EOF
  ln -s /etc/parser-target /etc/sudoers.d/parser-link
  mkdir /etc/sudoers.d/parser-subdirectory
  mkfifo /etc/sudoers.d/parser-fifo
  run ivan 'sudo -n /usr/bin/true'
  expect_rc 0
  end
}

begin parser-include-percent-literal && {
  install -m 0440 /dev/stdin /etc/parser%%file <<'EOF'
ivan ALL = NOPASSWD: /usr/bin/true
EOF
  install -m 0440 /dev/stdin /etc/sudoers.d/parser <<'EOF'
@include /etc/parser%%file
EOF
  run ivan 'sudo -n /usr/bin/true'
  expect_rc 0
  end
}

begin parser-quoted-and-bare-escape-lexing && {
  install -m 0440 /dev/stdin /etc/sudoers.d/parser <<'EOF'
\x69van ALL = NOPASSWD: /usr/bin/true
"\x69van" ALL = NOPASSWD: /usr/bin/false
Defaults:ivan passprompt=\x41
Defaults:ivan passprompt="\x42"
Defaults:ivan env_keep+="VAR\\NAME"
Defaults:ivan badpass_message="say \"hello\""
EOF
  /usr/sbin/visudo.ws -cqf /etc/sudoers.d/parser || fail "reference visudo rejected escape cases"
  run root "sudo -l -U ivan >'$WORK/escape-actual' && /usr/bin/sudo.ws -l -U ivan >'$WORK/escape-reference' && diff -u '$WORK/escape-reference' '$WORK/escape-actual'"
  expect_rc 0
  end
}
