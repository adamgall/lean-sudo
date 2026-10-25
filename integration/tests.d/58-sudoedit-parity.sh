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

sudoedit_chroot_setup() {
  sudoedit_parity_setup
  rm -rf /srv/sudoedit-jail
  mkdir -p /srv/sudoedit-jail/etc
  printf 'sudoers: files\npasswd: files\ngroup: files\n' >/srv/sudoedit-jail/etc/nsswitch.conf
  cp /etc/passwd /etc/group /srv/sudoedit-jail/etc/
  printf 'inside\n' >/srv/sudoedit-jail/etc/henryfile
  printf 'outside\n' >/etc/henryfile
}

begin sudoedit-chroot-rule && {
  sudoedit_chroot_setup
  printf 'henry ALL=(ALL:ALL) CHROOT=/srv/sudoedit-jail NOPASSWD: sudoedit\n' >/etc/sudoers.d/58-sudoedit
  run henry 'SUDO_EDITOR=/usr/local/bin/henry-editor sudoedit -n /etc/henryfile'
  expect_rc 0
  [[ $(cat /srv/sudoedit-jail/etc/henryfile) == inside ]] || fail 'rule root unexpectedly changed edit filesystem'
  [[ $(cat /etc/henryfile) == $'outside\nedited' ]] || fail 'rule CHROOT was not ignored'
  end
}

begin sudoedit-chroot-default-missing-editor && {
  sudoedit_chroot_setup
  printf 'Defaults:henry runchroot=/srv/sudoedit-jail\n' >>/etc/sudoers.d/58-sudoedit
  run henry 'SUDO_EDITOR=/usr/local/bin/henry-editor sudoedit -n /etc/henryfile'
  expect_rc 1
  expect_err_has 'sudoedit: unable to execute /usr/local/bin/henry-editor: No such file or directory'
  expect_err_has 'sudoedit: /etc/henryfile unchanged'
  [[ $(cat /srv/sudoedit-jail/etc/henryfile) == inside ]] || fail 'jailed original edited'
  [[ $(cat /etc/henryfile) == outside ]] || fail 'host original edited'
  end
}

begin sudoedit-chroot-rule-wildcard-does-not-allow-user-root && {
  sudoedit_chroot_setup
  printf 'henry ALL=(ALL:ALL) CHROOT=* NOPASSWD: sudoedit\n' >/etc/sudoers.d/58-sudoedit
  run henry 'SUDO_EDITOR=/usr/local/bin/henry-editor sudoedit -n -R /srv/sudoedit-jail /etc/henryfile'
  expect_rc 1
  expect_err_has 'you are not permitted to use the -R option with sudoedit'
  [[ $(cat /srv/sudoedit-jail/etc/henryfile) == inside ]] || fail 'jailed original edited'
  [[ $(cat /etc/henryfile) == outside ]] || fail 'host original edited'
  end
}

# Supply a distinct jailed editor. It can observe the jail, but the host temp
# pathname passed by sudoedit is deliberately absent from that filesystem.
sudoedit_chroot_editor() {
  python3 - <<'PY'
import pathlib, re, shutil, subprocess
root = pathlib.Path('/srv/sudoedit-jail')
paths = ['/bin/sh']
paths += re.findall(r'(/[^\s()]+)', subprocess.check_output(['ldd', '/bin/sh'], text=True))
for source in dict.fromkeys(paths):
    target = root / source.lstrip('/')
    target.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(source, target)
editor = root / 'usr/local/bin/henry-editor'
editor.parent.mkdir(parents=True, exist_ok=True)
editor.write_text('#!/bin/sh\nprintf "jailed-editor\\n"\n'
                  'test -f /etc/henryfile || exit 91\n'
                  'test ! -e "$1" || exit 92\n'
                  'printf "host-temp-unavailable\\n"\n')
editor.chmod(0o755)
PY
}

begin sudoedit-chroot-default-editor-only && {
  sudoedit_chroot_setup
  sudoedit_chroot_editor
  printf 'Defaults:henry runchroot=/srv/sudoedit-jail\n' >>/etc/sudoers.d/58-sudoedit
  run henry 'SUDO_EDITOR=/usr/local/bin/henry-editor sudoedit -n /etc/henryfile'
  expect_rc 0
  expect_out_line jailed-editor
  expect_out_line host-temp-unavailable
  expect_err_has 'sudoedit: /etc/henryfile unchanged'
  [[ $(cat /etc/henryfile) == outside ]] || fail 'host original changed'
  [[ $(cat /srv/sudoedit-jail/etc/henryfile) == inside ]] || fail 'jailed original changed'
  end
}

begin sudoedit-chroot-default-wildcard-user-root && {
  sudoedit_chroot_setup
  sudoedit_chroot_editor
  printf 'Defaults:henry runchroot=*\n' >>/etc/sudoers.d/58-sudoedit
  run henry 'SUDO_EDITOR=/usr/local/bin/henry-editor sudoedit -n -R /srv/sudoedit-jail /etc/henryfile'
  expect_rc 0
  expect_out_line jailed-editor
  expect_out_line host-temp-unavailable
  expect_err_has 'sudoedit: /etc/henryfile unchanged'
  [[ $(cat /etc/henryfile) == outside ]] || fail 'host original changed'
  [[ $(cat /srv/sudoedit-jail/etc/henryfile) == inside ]] || fail 'jailed original changed'
  end
}

begin sudoedit-chroot-rule-cannot-override-default && {
  sudoedit_chroot_setup
  sudoedit_chroot_editor
  printf 'Defaults:henry runchroot=/srv/sudoedit-jail\nhenry ALL=(ALL:ALL) CHROOT=/ NOPASSWD: sudoedit\n' >/etc/sudoers.d/58-sudoedit
  run henry 'SUDO_EDITOR=/usr/local/bin/henry-editor sudoedit -n /etc/henryfile'
  expect_rc 0
  expect_out_line jailed-editor
  expect_err_has 'sudoedit: /etc/henryfile unchanged'
  end
}

begin sudoedit-chroot-fixed-default-denies-identical-user-root && {
  sudoedit_chroot_setup
  printf 'Defaults:henry runchroot=/srv/sudoedit-jail\n' >>/etc/sudoers.d/58-sudoedit
  run henry 'SUDO_EDITOR=/usr/local/bin/henry-editor sudoedit -n -R /srv/sudoedit-jail /etc/henryfile'
  expect_rc 1
  expect_err_has 'you are not permitted to use the -R option with sudoedit'
  [[ $(cat /etc/henryfile) == outside ]] || fail 'denied request changed host original'
  end
}

# Match the exec jail boundary: absolute symlinks whose host realpath leaves the
# configured root are intentionally refused, even where sudo.ws follows them.
for escape_kind in editor parent; do
  begin "sudoedit-chroot-refuses-$escape_kind-escape" && {
    sudoedit_chroot_setup
    sudoedit_chroot_editor
    printf 'Defaults:henry runchroot=/srv/sudoedit-jail\n' >>/etc/sudoers.d/58-sudoedit
    if [[ $escape_kind == editor ]]; then
      mkdir -p /srv/sudoedit-jail/usr/bin
      cp /usr/bin/true /srv/sudoedit-jail/usr/bin/true
      rm -f /srv/sudoedit-jail/usr/local/bin/henry-editor
      ln -s /usr/bin/true /srv/sudoedit-jail/usr/local/bin/henry-editor
    else
      cp /srv/sudoedit-jail/usr/local/bin/henry-editor /srv/sudoedit-jail/bin/henry-editor
      rm -rf /srv/sudoedit-jail/usr/local/bin
      ln -s /bin /srv/sudoedit-jail/usr/local/bin
    fi
    run henry 'SUDO_EDITOR=/usr/local/bin/henry-editor sudoedit -n /etc/henryfile'
    if [[ $LABEL == reference ]]; then
      expect_rc 0
      expect_err_has 'sudoedit: /etc/henryfile unchanged'
    else
      expect_rc 1
      expect_err_has 'sudoedit: /usr/local/bin/henry-editor: command resolves outside the chroot directory'
    fi
    [[ $(cat /etc/henryfile) == outside ]] || fail 'root escape attempt changed host original'
    end
  }
done

begin sudoedit-execution-default-pty && {
  sudoedit_parity_setup
  cat >/usr/local/bin/henry-editor <<'EOF'
#!/bin/sh
printf 'editor-tty=%s\n' "$(tty)"
test "$(tty)" != "$PARENT_TTY"
EOF
  pty henry 'PARENT_TTY=$(tty); export PARENT_TTY; printf "parent-tty=%s\n" "$PARENT_TTY"; SUDO_EDITOR=/usr/local/bin/henry-editor sudoedit -n /etc/henryfile'
  expect_rc 0
  expect_out_has 'editor-tty=/dev/pts/'
  expect_out_has 'parent-tty=/dev/pts/'
  end
}

for logging in default tag; do
  begin "sudoedit-execution-iolog-$logging" && {
    sudoedit_parity_setup
    dir="$WORK/sudoedit-io-$logging"
    printf 'Defaults:henry iolog_dir="%s",!compress_io\n' "$dir" >>/etc/sudoers.d/58-sudoedit
    if [[ $logging == default ]]; then
      printf 'Defaults:henry log_output\n' >>/etc/sudoers.d/58-sudoedit
    else
      printf 'henry ALL=(ALL:ALL) NOPASSWD: LOG_OUTPUT: sudoedit\n' >>/etc/sudoers.d/58-sudoedit
    fi
    cat >/usr/local/bin/henry-editor <<'EOF'
#!/bin/sh
printf 'editor-output-marker\n'
printf 'edited\n' >>"$1"
EOF
    run henry 'SUDO_EDITOR=/usr/local/bin/henry-editor sudoedit -n /etc/henryfile'
    expect_rc 0
    expect_out_line editor-output-marker
    if [[ $logging == tag ]]; then
      # Like CHROOT, command-rule LOG_OUTPUT is not propagated for MODE_EDIT.
      [[ ! -e "$dir/seq" ]] || fail 'sudoedit unexpectedly honored LOG_OUTPUT tag'
    else
      run root "sudoreplay.ws -d '$dir' -l"
      expect_rc 0
      expect_out_has ' : henry : '
      expect_out_has 'COMMAND=/usr/local/bin/henry-editor -- /etc/henryfile'
      run root "sudoreplay.ws -n -d '$dir' 000001"
      expect_rc 0
      expect_out_has editor-output-marker
      [[ $(cat "$dir/00/00/01/stdout") == editor-output-marker ]] || fail 'editor stdout missing from I/O stream'
    fi
    end
  }
done

for timeout_kind in default rule; do
  begin "sudoedit-execution-timeout-$timeout_kind" && {
    sudoedit_parity_setup
    if [[ $timeout_kind == default ]]; then
      printf 'Defaults:henry command_timeout=1\n' >>/etc/sudoers.d/58-sudoedit
    else
      printf 'henry ALL=(ALL:ALL) TIMEOUT=1 NOPASSWD: sudoedit\n' >>/etc/sudoers.d/58-sudoedit
    fi
    cat >/usr/local/bin/henry-editor <<'EOF'
#!/bin/sh
printf 'edited\n' >>"$1"
exec /bin/sleep 4
EOF
    start=$SECONDS
    run henry 'SUDO_EDITOR=/usr/local/bin/henry-editor sudoedit -n /etc/henryfile'
    if [[ $timeout_kind == default ]]; then
      expect_rc_not 0
      [[ $((SECONDS - start)) -lt 4 ]] || fail 'editor timeout was not applied'
    else
      expect_rc 0
      [[ $((SECONDS - start)) -ge 3 ]] || fail 'sudoedit unexpectedly honored TIMEOUT rule'
    fi
    [[ $(cat /etc/henryfile) == $'original\nedited' ]] || fail 'timed-out editor changes were not copied back'
    end
  }
done

begin sudoedit-execution-resource-limits && {
  sudoedit_parity_setup
  printf 'Defaults:henry rlimit_nofile="128,256"\n' >>/etc/sudoers.d/58-sudoedit
  cat >/usr/local/bin/henry-editor <<'EOF'
#!/bin/bash
printf 'soft='; ulimit -Sn
printf 'hard='; ulimit -Hn
EOF
  run henry 'SUDO_EDITOR=/usr/local/bin/henry-editor sudoedit -n /etc/henryfile'
  expect_rc 0
  expect_out_line soft=128
  expect_out_line hard=256
  end
}

for utmp_mode in runas invoking; do
  begin "sudoedit-execution-utmp-$utmp_mode" && {
    sudoedit_parity_setup
    install -m 0664 /dev/null /run/utmp
    if [[ $utmp_mode == runas ]]; then
      printf 'Defaults:henry use_pty,set_utmp,utmp_runas\n' >>/etc/sudoers.d/58-sudoedit
      expected=gina
    else
      printf 'Defaults:henry use_pty,set_utmp,!utmp_runas\n' >>/etc/sudoers.d/58-sudoedit
      expected=henry
    fi
    cat >/usr/local/bin/henry-editor <<'EOF'
#!/usr/bin/python3
import sys
data = open('/run/utmp', 'rb').read()
print('utmp=' + ('present' if sys.argv[1].encode() in data else 'missing'))
EOF
    pty henry "SUDO_EDITOR='/usr/local/bin/henry-editor $expected' sudoedit -n -u gina /etc/henryfile"
    expect_rc 0
    expect_out_has utmp=present
    run root "python3 -c 'print(\"cleared\" if b\"$expected\" not in open(\"/run/utmp\", \"rb\").read() else \"present\")'"
    expect_rc 0
    expect_out_line cleared
    end
  }
done

for noexec_kind in default tag; do
  begin "sudoedit-execution-noexec-$noexec_kind" && {
    sudoedit_parity_setup
    if [[ $noexec_kind == default ]]; then
      printf 'Defaults:henry noexec\n' >>/etc/sudoers.d/58-sudoedit
    else
      printf 'henry ALL=(ALL:ALL) NOPASSWD: NOEXEC: sudoedit\n' >>/etc/sudoers.d/58-sudoedit
    fi
    cat >/usr/local/bin/henry-editor <<'EOF'
#!/bin/sh
if /usr/bin/true; then printf 'external-ran\n'; else printf 'external-blocked\n'; fi
EOF
    run henry 'SUDO_EDITOR=/usr/local/bin/henry-editor sudoedit -n /etc/henryfile'
    expect_rc 0
    if [[ $noexec_kind == default ]]; then
      expect_out_line external-blocked
    else
      expect_out_line external-ran
    fi
    end
  }
done

begin sudoedit-execution-closefrom && {
  sudoedit_parity_setup
  printf 'Defaults:henry closefrom=4\n' >>/etc/sudoers.d/58-sudoedit
  printf 'inherited-fd\n' >/tmp/sudoedit-extra-fd
  cat >/usr/local/bin/henry-editor <<'EOF'
#!/bin/sh
read -r value <&3 || exit 91
printf '%s\n' "$value"
EOF
  run henry 'SUDO_EDITOR=/usr/local/bin/henry-editor sudoedit -n /etc/henryfile 3</tmp/sudoedit-extra-fd'
  expect_rc 0
  expect_out_line inherited-fd
  rm -f /tmp/sudoedit-extra-fd
  end
}

for log_format in sudo json; do
  begin "sudoedit-execution-accept-metadata-$log_format" && {
    sudoedit_parity_setup
    log_file="$WORK/sudoedit-event-$log_format"
    printf 'Defaults:henry logfile="%s",log_format=%s,loglinelen=0\n' "$log_file" "$log_format" >>/etc/sudoers.d/58-sudoedit
    run henry 'SUDO_EDITOR=/usr/bin/true sudoedit -n /etc/henryfile'
    expect_rc 0
    if [[ $log_format == sudo ]]; then
      grep -qF 'COMMAND=/usr/bin/true -- /etc/henryfile' "$log_file" || fail "accept command metadata differs: $(cat "$log_file")"
    else
      python3 - "$log_file" <<'PY'
import json, sys
event = json.load(open(sys.argv[1]))['accept']
assert event['command'] == '/usr/bin/true', event
assert event['runargv'] == ['/usr/bin/true', '--', '/etc/henryfile'], event
PY
      [[ $? == 0 ]] || fail 'JSON accept editor metadata differs'
    fi
    end
  }
done

begin sudoedit-parity-relative-operand-unchanged && {
  sudoedit_parity_setup
  printf 'Defaults:henry runcwd=*\n' >>/etc/sudoers.d/58-sudoedit
  run henry 'cd /etc && SUDO_EDITOR=/usr/bin/true sudo -ne -D /tmp ./henryfile'
  expect_rc 0
  [[ $ERR == 'sudo: ./henryfile unchanged' ]] || fail 'unchanged diagnostic lost original operand spelling'
  [[ $(cat /etc/henryfile) == original ]] || fail 'editor cwd changed original file resolution'
  end
}

begin sudoedit-parity-relative-operand-open-error && {
  sudoedit_parity_setup
  ln -s /etc/henryfile /etc/henrylink
  run henry 'cd /etc && SUDO_EDITOR=/usr/bin/true sudoedit -n ./henrylink'
  expect_rc 1
  [[ $ERR == 'sudoedit: ./henrylink: editing symbolic links is not permitted' ]] || fail 'open diagnostic lost original operand spelling'
  end
}
