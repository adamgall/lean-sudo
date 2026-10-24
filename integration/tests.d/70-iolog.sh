# These sessions are consumed by the distribution's unmodified sudoreplay.
iolog_policy() {
  local dir=$1 options=$2
  install -m 0440 /dev/stdin /etc/sudoers.d/iolog <<EOF
Defaults iolog_dir="$dir", $options
ivan ALL=(ALL) NOPASSWD: ALL
EOF
}

begin iolog-output-replay-list && {
  dir="$WORK/io-output"
  iolog_policy "$dir" 'log_output, !compress_io'
  run alice 'printf "alicepw\n" | sudo -S /usr/bin/echo hi'
  expect_rc 0
  expect_out_line hi
  run root "sudoreplay.ws -d '$dir' -l"
  expect_rc 0
  expect_out_has ' : alice : '
  expect_out_has 'COMMAND=/usr/bin/echo hi'
  run root "sudoreplay.ws -n -d '$dir' 000001"
  expect_rc 0
  # The first "hi" is in replay's banner; the second must come from the stream.
  expect_out_has hihi
  [[ $(cat "$dir/seq") == 000001 ]] || fail 'initial sequence is not 000001'
  [[ -s "$dir/00/00/01/log.json" && -s "$dir/00/00/01/log" ]] || fail 'missing metadata'
  end
}

begin iolog-tag-and-sequence && {
  dir="$WORK/io-tag"
  install -m 0440 /dev/stdin /etc/sudoers.d/iolog <<EOF
Defaults iolog_dir="$dir", !compress_io
ivan ALL=(ALL) NOPASSWD: LOG_OUTPUT: ALL
EOF
  run ivan 'sudo /usr/bin/echo first; sudo /usr/bin/echo second'
  expect_rc 0
  [[ $(cat "$dir/seq") == 000002 ]] || fail 'sequence did not increment'
  run root "sudoreplay.ws -n -d '$dir' 000002"
  expect_rc 0
  expect_out_has second
  end
}

begin iolog-input-plain && {
  dir="$WORK/io-input"
  iolog_policy "$dir" 'log_input, !compress_io'
  run ivan 'printf "recorded input\n" | sudo /usr/bin/cat'
  expect_rc 0
  expect_out_line 'recorded input'
  [[ $(cat "$dir/00/00/01/stdin") == 'recorded input' ]] || fail 'stdin not recorded'
  [[ ! -e "$dir/00/00/01/stdout" ]] || fail 'disabled stdout was logged'
  end
}

begin iolog-compression && {
  dir="$WORK/io-compressed"
  iolog_policy "$dir" 'log_output, compress_io, iolog_flush'
  run ivan 'sudo /usr/bin/echo compressed'
  expect_rc 0
  gzip -t "$dir/00/00/01/stdout" || fail 'stdout is not gzip'
  gzip -t "$dir/00/00/01/timing" || fail 'timing is not gzip'
  run root "sudoreplay.ws -n -d '$dir' 000001"
  expect_rc 0
  expect_out_has compressed
  end
}

begin iolog-permissions && {
  dir="$WORK/io-mode"
  iolog_policy "$dir" 'log_output, !compress_io, iolog_mode=0640, iolog_group=adm'
  run ivan 'sudo /usr/bin/echo modes'
  expect_rc 0
  [[ $(stat -c %a "$dir/00/00/01") == 750 ]] || fail 'session directory mode'
  [[ $(stat -c %a "$dir/00/00/01/stdout") == 640 ]] || fail 'stream file mode'
  [[ $(stat -c %G "$dir/00/00/01/stdout") == adm ]] || fail 'stream group'
  end
}

begin iolog-failure-closed-and-ignore && {
  dir="/proc/lean-sudo-iolog-unwritable"
  iolog_policy "$dir" 'log_output'
  run ivan "sudo /usr/bin/touch '$WORK/should-not-run'"
  expect_rc_not 0
  [[ ! -e "$WORK/should-not-run" ]] || fail 'command ran without its required log'
  end
}

begin iolog-ignore-open-error && {
  iolog_policy "/proc/lean-sudo-iolog-unwritable" 'log_output, ignore_iolog_errors'
  run ivan 'sudo /usr/bin/echo allowed'
  expect_rc 0
  expect_out_line allowed
  end
}

begin iolog-stream-override && {
  dir="$WORK/io-stream"
  iolog_policy "$dir" 'log_output, !log_stdout, !compress_io'
  run ivan 'sudo /bin/sh -c "echo stdout; echo stderr >&2"'
  expect_rc 0
  [[ ! -e "$dir/00/00/01/stdout" ]] || fail 'log_stdout override ignored'
  [[ $(cat "$dir/00/00/01/stderr") == stderr ]] || fail 'stderr stream missing'
  end
}

begin iolog-expanded-path && {
  dir="$WORK/io-expanded"
  iolog_policy "$dir" 'log_output, !compress_io, iolog_file="%{user}/%{runas_user}/%{command}/%Y/%{seq}"'
  run ivan 'sudo /usr/bin/echo expanded'
  expect_rc 0
  [[ -s "$dir/ivan/root/echo/$(date +%Y)/00/00/01/log.json" ]] || fail 'named or time path escape'
  end
}

begin iolog-sequence-wrap && {
  dir="$WORK/io-wrap"
  iolog_policy "$dir" 'log_output, !compress_io, maxseq=1'
  run ivan 'sudo /usr/bin/echo first; sudo /usr/bin/echo wrapped'
  expect_rc 0
  [[ $(cat "$dir/seq") == 000001 ]] || fail 'maxseq did not wrap'
  [[ $(cat "$dir/00/00/01/stdout") == wrapped ]] || fail 'wrapped session missing'
  end
}

begin iolog-tty-password-filter && {
  dir="$WORK/io-password"
  iolog_policy "$dir" 'log_input, log_output, !log_passwords, !compress_io'
  pty ivan "sudo /bin/sh -c 'stty -echo; printf \"Password: \"; read answer; stty echo; echo done'" \
    -e 'Password: ' -s 'secretvalue\r'
  expect_rc 0
  grep -q 'secretvalue' "$dir/00/00/01/ttyin" && fail 'password leaked into ttyin'
  grep -q '\*\*\*' "$dir/00/00/01/ttyin" || fail 'password input was not masked'
  run root "sudoreplay.ws -n -d '$dir' 000001"
  expect_rc 0
  expect_out_has done
  end
}

begin iolog-tty-password-explicit && {
  dir="$WORK/io-password-enabled"
  iolog_policy "$dir" 'log_input, log_output, log_passwords, !compress_io'
  pty ivan "sudo /bin/sh -c 'stty -echo; printf \"Password: \"; read answer; stty echo; echo done'" \
    -e 'Password: ' -s 'secretvalue\r'
  expect_rc 0
  grep -q 'secretvalue' "$dir/00/00/01/ttyin" || fail 'explicit log_passwords input missing'
  end
}
