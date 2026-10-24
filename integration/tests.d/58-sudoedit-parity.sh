# sudo.ws 1.9.17p2 src/sudo_edit.c and plugins/sudoers/editor.c parity.
# Every case runs unchanged against the installed implementation and reference.
sudoedit_parity_setup() {
  edit_setup
  printf 'henry ALL=(ALL:ALL) NOPASSWD: sudoedit\n' >/etc/sudoers.d/58-sudoedit
  chmod 0440 /etc/sudoers.d/58-sudoedit
  touch -d '2001-02-03 04:05:06.123456789 UTC' /etc/henryfile
}

for base in nginx.conf archive.tar.gz .profile file file. suffix.XXXXXXXX; do
  begin "sudoedit-parity-temp-name-$base" && {
    sudoedit_parity_setup
    printf 'original\n' >"/etc/$base"
    XENV=(SUDO_EDITOR='/usr/bin/printf %s\\n')
    run henry "sudoedit -n /etc/$base"
    expect_rc 0
    if [[ $base == *.* ]]; then
      stem=${base%.*}; suffix=.${base##*.}
    else
      stem=$base.; suffix=
    fi
    temp_base=${OUT##*/}
    [[ $OUT == /var/tmp/* && $temp_base == "$stem"????????"$suffix" ]] || fail "temporary basename does not retain suffix: $OUT"
    rm -f "/etc/$base"
    end
  }
done

begin sudoedit-parity-temp-original-mtime && {
  sudoedit_parity_setup
  XENV=(SUDO_EDITOR='/usr/bin/stat -c %y')
  run henry 'sudoedit -n /etc/henryfile'
  expect_rc 0
  expect_out_line '2001-02-03 04:05:06.123456789 +0000'
  expect_err_has 'sudoedit: /etc/henryfile unchanged'
  end
}

begin sudoedit-parity-touch-writes-back && {
  sudoedit_parity_setup
  run henry 'SUDO_EDITOR=/usr/bin/touch sudoedit -n /etc/henryfile'
  expect_rc 0
  expect_err_lacks unchanged
  [[ $(stat -c %Y /etc/henryfile) != 981173106 ]] || fail 'touch did not write back'
  [[ $(cat /etc/henryfile) == original ]] || fail 'touch altered bytes'
  end
}

begin sudoedit-parity-nanosecond-change-writes-back && {
  sudoedit_parity_setup
  cat >/usr/local/bin/henry-editor <<'EOF'
#!/usr/bin/python3
import os, sys
p = sys.argv[1]
s = os.stat(p)
os.utime(p, ns=(s.st_atime_ns, s.st_mtime_ns + 1))
EOF
  run henry 'SUDO_EDITOR=/usr/local/bin/henry-editor sudoedit -n /etc/henryfile'
  expect_rc 0
  expect_err_lacks unchanged
  [[ $(stat -c %Y /etc/henryfile) != 981173106 ]] || fail 'nanosecond change did not write back'
  end
}

begin sudoedit-parity-same-size-mtime-skips-different-bytes && {
  sudoedit_parity_setup
  cat >/usr/local/bin/henry-editor <<'EOF'
#!/usr/bin/python3
import os, sys
p = sys.argv[1]
s = os.stat(p)
with open(p, 'wb') as f:
    f.write(b'replaced\n')
os.utime(p, ns=(s.st_atime_ns, s.st_mtime_ns))
EOF
  run henry 'SUDO_EDITOR=/usr/local/bin/henry-editor sudoedit -n /etc/henryfile'
  expect_rc 0
  expect_err_has 'sudoedit: /etc/henryfile unchanged'
  [[ $(cat /etc/henryfile) == original ]] || fail 'size+mtime equality did not skip copyback'
  end
}

begin sudoedit-parity-size-change-same-mtime-writes-back && {
  sudoedit_parity_setup
  cat >/usr/local/bin/henry-editor <<'EOF'
#!/usr/bin/python3
import os, sys
p = sys.argv[1]
s = os.stat(p)
with open(p, 'ab') as f:
    f.write(b'edited\n')
os.utime(p, ns=(s.st_atime_ns, s.st_mtime_ns))
EOF
  run henry 'SUDO_EDITOR=/usr/local/bin/henry-editor sudoedit -n /etc/henryfile'
  expect_rc 0
  expect_err_lacks unchanged
  [[ $(cat /etc/henryfile) == $'original\nedited' ]] || fail 'size change skipped copyback'
  end
}

begin sudoedit-parity-new-unchanged-file-not-created && {
  sudoedit_parity_setup
  XENV=(SUDO_EDITOR='/usr/bin/stat -c %Y')
  run henry 'sudoedit -n /etc/henrynew'
  expect_rc 0
  expect_out_line 0
  expect_err_has 'sudoedit: /etc/henrynew unchanged'
  [[ ! -e /etc/henrynew ]] || fail 'empty unchanged file was created'
  end
}

for status in 0 7; do
  begin "sudoedit-parity-multiple-open-failure-status-$status" && {
    sudoedit_parity_setup
    ln -s /etc/henryfile /etc/henrylink
    printf '#!/bin/sh\nprintf "edited\\n" >>"$1"\nexit %s\n' "$status" >/usr/local/bin/henry-editor
    run henry 'SUDO_EDITOR=/usr/local/bin/henry-editor sudoedit -n /etc/henrylink /etc/henryfile'
    expect_rc "$status"
    expect_err_has '/etc/henrylink: editing symbolic links is not permitted'
    [[ $(cat /etc/henryfile) == $'original\nedited' ]] || fail 'valid file was not edited'
    end
  }
  begin "sudoedit-parity-writeback-failure-overrides-status-$status" && {
    sudoedit_parity_setup
    printf '#!/bin/sh\nprintf "edited\\n" >>"$1"\nexit %s\n' "$status" >/usr/local/bin/henry-editor
    run henry 'SUDO_EDITOR=/usr/local/bin/henry-editor sudoedit -n -u gina /etc/henryfile'
    expect_rc 1
    expect_err_has 'Permission denied'
    expect_err_has 'contents of edit session left in '
    [[ $(cat /etc/henryfile) == original ]] || fail 'failed copyback changed original'
    saved=${ERR##*contents of edit session left in }
    [[ -f $saved && $(cat "$saved") == $'original\nedited' ]] || fail 'edited temporary copy not retained'
    [[ ! -f $saved ]] || rm -f "$saved"
    end
  }
done

begin sudoedit-parity-multiple-writeback-continues && {
  sudoedit_parity_setup
  printf 'second\n' >/etc/henrysecond
  chown gina:gina /etc/henrysecond
  cat >/usr/local/bin/henry-editor <<'EOF'
#!/bin/sh
for file do printf 'edited\n' >>"$file"; done
exit 7
EOF
  run henry 'SUDO_EDITOR=/usr/local/bin/henry-editor sudoedit -n -u gina /etc/henryfile /etc/henrysecond'
  expect_rc 1
  [[ $(cat /etc/henrysecond) == $'second\nedited' ]] || fail 'copyback stopped after first error'
  saved=${ERR##*contents of edit session left in }
  [[ ! -f $saved ]] || rm -f "$saved"
  rm -f /etc/henrysecond
  end
}

for variable in SUDO_EDITOR VISUAL EDITOR; do
  begin "sudoedit-parity-no-env-editor-$variable" && {
    sudoedit_parity_setup
    printf 'Defaults:henry !env_editor\n' >>/etc/sudoers.d/58-sudoedit
    XENV=("$variable=/usr/local/bin/henry-editor")
    run henry 'sudoedit -n /etc/henryfile'
    expect_rc 0
    [[ $(cat /etc/henryfile) == $'original\nedited' ]] || fail 'editor environment variable was ignored'
    end
  }
done

# find_editor runs before env_swap_old: secure_path has already replaced PATH.
for path_mode in secure user exempt; do
  begin "sudoedit-parity-editor-path-$path_mode" && {
    sudoedit_parity_setup
    mkdir -p /home/henry/bin
    cp /usr/local/bin/henry-editor /home/henry/bin/parity-editor
    printf 'Defaults:henry editor=/no-parity-editor\n' >>/etc/sudoers.d/58-sudoedit
    if [[ $path_mode == user ]]; then
      printf 'Defaults:henry !secure_path\n' >>/etc/sudoers.d/58-sudoedit
    elif [[ $path_mode == exempt ]]; then
      printf 'Defaults:henry exempt_group=henry\n' >>/etc/sudoers.d/58-sudoedit
    fi
    run henry 'PATH=/home/henry/bin:/usr/bin:/bin SUDO_EDITOR=parity-editor sudoedit -n /etc/henryfile'
    if [[ $path_mode == secure ]]; then
      expect_rc 1
      [[ $ERR == 'sudoedit: parity-editor: command not found' ]] || fail 'secure_path did not override user PATH'
      [[ $(cat /etc/henryfile) == original ]] || fail 'missing editor modified file'
    else
      expect_rc 0
      [[ $(cat /etc/henryfile) == $'original\nedited' ]] || fail 'user PATH did not resolve editor'
    fi
    rm -f /home/henry/bin/parity-editor
    end
  }
done

begin sudoedit-parity-relative-editor-path && {
  sudoedit_parity_setup
  cp /usr/local/bin/henry-editor /home/henry/parity-editor
  run henry 'SUDO_EDITOR=./parity-editor sudoedit -n /etc/henryfile'
  expect_rc 0
  [[ $(cat /etc/henryfile) == $'original\nedited' ]] || fail 'relative editor did not run'
  rm -f /home/henry/parity-editor
  end
}

begin sudoedit-parity-quoted-escaped-words && {
  sudoedit_parity_setup
  cat >'/usr/local/bin/parity editor' <<'EOF'
#!/bin/sh
printf '<%s>\n' "$1" "$2" "$3" "$4" "$5"
printf 'edited\n' >>"$6"
EOF
  chmod 0755 '/usr/local/bin/parity editor'
  XENV=("SUDO_EDITOR='/usr/local/bin/parity editor' 'two words' back\\ slash 'a\\'b' mid\"quote ''")
  run henry 'sudoedit -n /etc/henryfile'
  expect_rc 0
  expect_out_line '<two words>'
  expect_out_line '<back slash>'
  expect_out_line "<a'b>"
  expect_out_line '<mid"quote>'
  expect_out_line '<>'
  [[ $(cat /etc/henryfile) == $'original\nedited' ]] || fail 'quoted editor did not edit'
  rm -f '/usr/local/bin/parity editor'
  end
}

begin sudoedit-parity-rejects-decoded-separator && {
  sudoedit_parity_setup
  editor="/usr/bin/true '\\-\\-' /etc/hostname"
  XENV=("SUDO_EDITOR=$editor" VISUAL=/usr/bin/true)
  run henry 'sudoedit -n /etc/henryfile'
  expect_rc 1
  [[ $ERR == "sudoedit: ignoring editor: $editor"$'\n''sudoedit: editor arguments may not contain "--"' ]] || fail 'separator rejection diagnostic differs'
  [[ $(cat /etc/henryfile) == original ]] || fail 'injection changed file'
  end
}

begin sudoedit-parity-missing-editor-separator-falls-through && {
  sudoedit_parity_setup
  XENV=(SUDO_EDITOR='no-such-parity-editor -- /etc/hostname' VISUAL=/usr/bin/true)
  run henry 'sudoedit -n /etc/henryfile'
  expect_rc 0
  expect_err_lacks 'ignoring editor'
  expect_err_has 'unchanged'
  end
}

for source in environment defaults; do
  begin "sudoedit-parity-missing-editor-$source" && {
    sudoedit_parity_setup
    printf 'Defaults:henry editor=/no-parity-editor:/no-second-editor\n' >>/etc/sudoers.d/58-sudoedit
    if [[ $source == environment ]]; then
      XENV=(SUDO_EDITOR=no-first-editor VISUAL=no-last-editor)
      expected=no-last-editor
    else
      expected=/no-parity-editor:/no-second-editor
    fi
    run henry 'sudoedit -n /etc/henryfile'
    expect_rc 1
    [[ $ERR == "sudoedit: $expected: command not found" ]] || fail 'missing editor diagnostic differs'
    end
  }
done

begin sudoedit-parity-temp-creation-failure-is-fatal && {
  sudoedit_parity_setup
  printf -v longname '%0250d' 0
  printf 'second\n' >"/etc/$longname"
  run henry "SUDO_EDITOR=/usr/local/bin/henry-editor sudoedit -n /etc/henryfile /etc/$longname"
  expect_rc 1
  expect_err_has 'File name too long'
  [[ $(cat /etc/henryfile) == original ]] || fail 'editor ran after temporary creation failed'
  [[ $(cat "/etc/$longname") == second ]] || fail 'temporary failure changed second original'
  rm -f "/etc/$longname"
  end
}

begin sudoedit-parity-editor-path-unset && {
  sudoedit_parity_setup
  printf 'Defaults:henry !secure_path,editor=/no-parity-editor\n' >>/etc/sudoers.d/58-sudoedit
  run henry '/usr/bin/env -u PATH SUDO_EDITOR=touch /usr/bin/sudoedit -n /etc/henryfile'
  expect_rc 0
  expect_err_lacks unchanged
  [[ $(stat -c %Y /etc/henryfile) != 981173106 ]] || fail 'default PATH did not resolve editor'
  end
}

begin sudoedit-parity-sudo-e-unchanged-prefix && {
  sudoedit_parity_setup
  run henry 'SUDO_EDITOR=/usr/bin/true /usr/bin/sudo -ne /etc/henryfile'
  expect_rc 0
  [[ $ERR == 'sudo: /etc/henryfile unchanged' ]] || fail 'sudo -e lost frontend diagnostic prefix'
  end
}

begin sudoedit-parity-sudo-e-open-error-prefix && {
  sudoedit_parity_setup
  ln -s /etc/henryfile /etc/henrylink
  run henry 'SUDO_EDITOR=/usr/bin/true /usr/bin/sudo -ne /etc/henrylink'
  expect_rc 1
  [[ $ERR == 'sudo: /etc/henrylink: editing symbolic links is not permitted' ]] || fail 'sudo -e open error lost frontend prefix'
  end
}

begin sudoedit-parity-sudo-e-editor-error-prefix && {
  sudoedit_parity_setup
  run henry 'SUDO_EDITOR="/usr/bin/true -- /etc/hostname" /usr/bin/sudo -ne /etc/henryfile'
  expect_rc 1
  [[ $ERR == $'sudo: ignoring editor: /usr/bin/true -- /etc/hostname\nsudo: editor arguments may not contain "--"' ]] || fail 'sudo -e editor error lost frontend prefix'
  end
}
