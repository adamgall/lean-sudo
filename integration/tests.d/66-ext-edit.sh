ext_edit_setup() {
  printf 'ivan ALL=(ALL:ALL) NOPASSWD: ALL\n' >/etc/sudoers.d/66-ext-edit
  chmod 0440 /etc/sudoers.d/66-ext-edit
  rm -rf /tmp/ext-edit-bar /ext-edit-bar /ext-edit-baz /tmp/ext-edit-foo.sh /var/tmp/ext-edit-foo.sh
  mkdir -m 0755 /tmp/ext-edit-bar
  mkdir -m 0777 /ext-edit-bar
  mkdir -m 0555 /ext-edit-baz
  chown ivan /ext-edit-baz
  printf 'original\n' >/etc/ext-edit-file
  chmod 0644 /etc/ext-edit-file
  rm -f /tmp/ext-edit-temp
  cat >/usr/local/bin/ext-edit-append <<'EOF'
#!/bin/sh
printf '%s' "$1" >/tmp/ext-edit-temp
printf 'edited\n' >>"$1"
EOF
  chmod 0755 /usr/local/bin/ext-edit-append
}

ext_edit_cleanup() {
  [[ ! -f /tmp/ext-edit-temp ]] || rm -rf "$(cat /tmp/ext-edit-temp)"
  rm -rf /tmp/ext-edit-bar /ext-edit-bar /ext-edit-baz /tmp/ext-edit-temp /etc/ext-edit-file \
    /etc/sudoers.d/66-ext-edit /usr/local/bin/ext-edit-append /usr/local/bin/ext-edit-editor
}

for target in /tmp/ext-edit-foo.sh /tmp/ext-edit-bar/foo.sh /var/tmp/ext-edit-foo.sh \
    /ext-edit-bar/foo.sh /ext-edit-baz/foo.sh /tmp/ext-edit-bar/nodir/foo.sh; do
  name=${target#/}
  begin "ext-sudoedit-writable-path-${name//\//-}" && {
    ext_edit_setup
    XENV=(SUDO_EDITOR=/usr/local/bin/ext-edit-append)
    run ivan "sudoedit -n $target"
    expect_rc 1
    expect_out_empty
    case $target in
      /tmp/ext-edit-bar/*) want="sudoedit: $target: No such file or directory";;
      *) want="sudoedit: $target: editing files in a writable directory is not permitted";;
    esac
    [[ $ERR == "$want" ]] || fail "stderr: expected exactly '$want'"
    [[ ! -e $target ]] || fail "$target was created"
    [[ ! -e /tmp/ext-edit-temp ]] || fail 'editor was run'
    ext_edit_cleanup
    end
  }
done

begin ext-sudoedit-existing-file-below-writable-ancestor && {
  ext_edit_setup
  printf 'original\n' >/tmp/ext-edit-bar/foo.sh
  chmod 0644 /tmp/ext-edit-bar/foo.sh
  XENV=(SUDO_EDITOR=/usr/local/bin/ext-edit-append)
  run ivan 'sudoedit -n /tmp/ext-edit-bar/foo.sh'
  expect_rc 0
  [[ -z $ERR ]] || fail 'stderr: expected empty'
  [[ $(cat /tmp/ext-edit-bar/foo.sh) == $'original\nedited' ]] || fail 'edit not written back'
  ext_edit_cleanup
  end
}

for kind in deleted symlink directory fifo mode0644 mode04600; do
  begin "ext-sudoedit-temp-$kind-left-unmodified" && {
    ext_edit_setup
    case $kind in
      deleted) action='rm "$1"';;
      symlink) action='rm "$1"; ln -s /etc/hostname "$1"';;
      directory) action='rm "$1"; mkdir "$1"';;
      fifo) action='rm "$1"; mkfifo "$1"';;
      mode0644) action='printf "edited\n" >>"$1"; chmod 0644 "$1"';;
      mode04600) action='printf "edited\n" >>"$1"; chmod 04600 "$1"';;
    esac
    printf '#!/bin/sh\nprintf "%%s" "$1" >/tmp/ext-edit-temp\n%s\n' "$action" \
      >/usr/local/bin/ext-edit-editor
    chmod 0755 /usr/local/bin/ext-edit-editor
    XENV=(SUDO_EDITOR=/usr/local/bin/ext-edit-editor)
    run ivan 'sudoedit -n /etc/ext-edit-file'
    expect_rc 1
    expect_out_empty
    temp=$(cat /tmp/ext-edit-temp 2>/dev/null)
    case $kind in
      directory|fifo) want="sudoedit: $temp: not a regular file"$'\n';;
      mode0644) want="sudoedit: $temp: bad file mode: 0644"$'\n';;
      mode04600) want="sudoedit: $temp: bad file mode: 04600"$'\n';;
      *) want=;;
    esac
    want+='sudoedit: /etc/ext-edit-file left unmodified'
    [[ $ERR == "$want" ]] || fail "stderr: expected exactly '$want'"
    [[ $(cat /etc/ext-edit-file) == original ]] || fail 'original was modified'
    ext_edit_cleanup
    end
  }
done

for kind in mode000 mode644 missing bare; do
  begin "ext-sudoedit-env-editor-falls-back-$kind" && {
    ext_edit_setup
    printf 'Defaults editor=/usr/local/bin/ext-edit-append\n' >>/etc/sudoers.d/66-ext-edit
    env_editor=/tmp/ext-edit-env-editor
    rm -f "$env_editor"
    printf '#!/bin/sh\nexit 3\n' >"$env_editor"
    case $kind in
      mode000) chmod 0000 "$env_editor";;
      mode644) chmod 0644 "$env_editor";;
      missing) rm -f "$env_editor";;
      bare) env_editor=ext-no-such-editor;;
    esac
    XENV=(SUDO_EDITOR="$env_editor")
    run ivan 'sudoedit -n /etc/ext-edit-file'
    expect_rc 0
    [[ -z $ERR ]] || fail 'stderr: expected empty'
    [[ $(cat /etc/ext-edit-file) == $'original\nedited' ]] || fail 'fallback editor not used'
    rm -f /tmp/ext-edit-env-editor
    ext_edit_cleanup
    end
  }
done

begin ext-sudoedit-temp-name-randomizes-all-x && {
  ext_edit_setup
  printf 'original\n' >/etc/ext-edit-name.conf
  : >/tmp/ext-edit-names
  chmod 0666 /tmp/ext-edit-names
  printf '#!/bin/sh\nprintf "%%s\\n" "$1" >>/tmp/ext-edit-names\n' >/usr/local/bin/ext-edit-editor
  chmod 0755 /usr/local/bin/ext-edit-editor
  XENV=(SUDO_EDITOR=/usr/local/bin/ext-edit-editor)
  for _ in 1 2 3 4 5 6; do
    run ivan 'sudoedit -n /etc/ext-edit-name.conf'
    expect_rc 0
  done
  [[ $(wc -l </tmp/ext-edit-names) == 6 ]] || fail 'editor did not record six temporary names'
  if grep -qvxE '/var/tmp/ext-edit-name[A-Za-z0-9]{8}\.conf' /tmp/ext-edit-names; then
    fail "temporary name outside template: $(cat /tmp/ext-edit-names)"
  fi
  if ! grep -qvxE '/var/tmp/ext-edit-nameXX[A-Za-z0-9]{6}\.conf' /tmp/ext-edit-names; then
    fail "first two template characters never randomized: $(cat /tmp/ext-edit-names)"
  fi
  rm -f /etc/ext-edit-name.conf /tmp/ext-edit-names
  ext_edit_cleanup
  end
}

for target in foo ./foo sub/foo ../etc/hostname; do
  begin "ext-sudoedit-deleted-cwd-relative-${target//[\/.]/_}" && {
    ext_edit_setup
    rm -rf /tmp/ext-edit-gone
    XENV=(SUDO_EDITOR=/usr/local/bin/ext-edit-append)
    gone=/tmp/ext-edit-gone
    run ivan "mkdir $gone && cd $gone && rmdir $gone && sudoedit -n $target"
    expect_rc 1
    expect_out_empty
    case $target in
      foo|./foo) want="sudoedit: $target: editing files in a writable directory is not permitted";;
      *) want="sudoedit: $target: No such file or directory";;
    esac
    [[ $ERR == "$want" ]] || fail "stderr: expected exactly '$want'"
    [[ ! -e /tmp/ext-edit-temp ]] || fail 'editor was run'
    rm -rf /tmp/ext-edit-gone
    ext_edit_cleanup
    end
  }
done

for user in root ivan; do
  begin "ext-sudoedit-umask-777-$user" && {
    ext_edit_setup
    rm -f /var/tmp/ext-edit-file.*
    XENV=(SUDO_EDITOR=/usr/bin/true)
    run "$user" 'umask 777; sudoedit -n /etc/ext-edit-file'
    expect_rc 1
    expect_out_empty
    tail='sudoedit: /etc/ext-edit-file left unmodified'
    if [[ $user == root ]]; then
      re='^sudoedit: /var/tmp/ext-edit-file\.[A-Za-z0-9]{8}: bad file mode: 00'$'\n'"$tail\$"
      [[ $ERR =~ $re ]] || fail "stderr: expected bad file mode 00 then '$tail'"
    else
      [[ $ERR == "$tail" ]] || fail "stderr: expected exactly '$tail'"
    fi
    [[ $(cat /etc/ext-edit-file) == original ]] || fail 'original was modified'
    rm -f /var/tmp/ext-edit-file.*
    ext_edit_cleanup
    end
  }
done
