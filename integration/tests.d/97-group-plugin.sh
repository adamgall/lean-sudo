# Real Ubuntu sudo group plugins, using the same expectations for both binaries.
group_plugin_policy() {
  printf 'admins:x:42001:ivan\nothers:x:42002:alice\n#42003:x:42003:ivan\n' >/etc/sudo-group
  chmod 0644 /etc/sudo-group
  printf 'Defaults group_plugin="%s"\n%s\n' "$1" "$2" >/etc/sudoers.d/group-plugin
  chmod 0440 /etc/sudoers.d/group-plugin
}

begin group-plugin-file-member && {
  group_plugin_policy 'group_file.so /etc/sudo-group' '%:admins ALL=(ALL) NOPASSWD: /usr/bin/id'
  run ivan 'sudo -n /usr/bin/id -u'
  expect_rc 0; expect_out_line 0; [[ -z $ERR ]] || fail "unexpected stderr: $ERR"
  end
}
begin group-plugin-file-nonmember && {
  group_plugin_policy 'group_file.so /etc/sudo-group' '%:others ALL=(ALL) NOPASSWD: /usr/bin/id'
  run ivan 'sudo -n /usr/bin/id -u'
  expect_rc 1; expect_out_empty
  end
}
begin group-plugin-file-absolute && {
  group_plugin_policy '/usr/libexec/sudo/group_file.so   /etc/sudo-group' '%:admins ALL=(ALL) NOPASSWD: /usr/bin/id'
  run ivan 'sudo -n /usr/bin/id -u'
  expect_rc 0; expect_out_line 0
  end
}
begin group-plugin-file-numeric && {
  group_plugin_policy 'group_file.so /etc/sudo-group' '%:#42003 ALL=(ALL) NOPASSWD: /usr/bin/id'
  run ivan 'sudo -n /usr/bin/id -u'
  expect_rc 0; expect_out_line 0
  end
}
begin group-plugin-negated-member && {
  group_plugin_policy 'group_file.so /etc/sudo-group' 'ALL,!%:admins ALL=(ALL) NOPASSWD: /usr/bin/id'
  run ivan 'sudo -n /usr/bin/id -u'
  expect_rc 1; expect_out_empty
  end
}
begin group-plugin-negated-nonmember && {
  group_plugin_policy 'group_file.so /etc/sudo-group' 'ALL,!%:others ALL=(ALL) NOPASSWD: /usr/bin/id'
  run ivan 'sudo -n /usr/bin/id -u'
  expect_rc 0; expect_out_line 0
  end
}
begin group-plugin-alias && {
  group_plugin_policy 'group_file.so /etc/sudo-group' $'User_Alias PLUGIN = %:admins\nPLUGIN ALL=(ALL) NOPASSWD: /usr/bin/id'
  run ivan 'sudo -n /usr/bin/id -u'
  expect_rc 0; expect_out_line 0
  end
}
begin group-plugin-runas && {
  group_plugin_policy 'group_file.so /etc/sudo-group' 'ivan ALL=(%:others) NOPASSWD: /usr/bin/id'
  run ivan 'sudo -n -u alice /usr/bin/id -un'
  expect_rc 0; expect_out_line alice
  end
}
begin group-plugin-system-name && {
  group_plugin_policy 'system_group.so' '%:pluginunix ALL=(ALL) NOPASSWD: /usr/bin/id'
  groupadd -f pluginunix; gpasswd -a ivan pluginunix >/dev/null
  run ivan 'sudo -n /usr/bin/id -u'
  expect_rc 0; expect_out_line 0
  gpasswd -d ivan pluginunix >/dev/null
  end
}
begin group-plugin-system-numeric && {
  groupadd -f pluginunix; gpasswd -a ivan pluginunix >/dev/null
  group_plugin_policy 'system_group.so' "%:#$(getent group pluginunix | cut -d: -f3) ALL=(ALL) NOPASSWD: /usr/bin/id"
  run ivan 'sudo -n /usr/bin/id -u'
  expect_rc 0; expect_out_line 0
  gpasswd -d ivan pluginunix >/dev/null
  end
}
begin group-plugin-unix-default-no-query && {
  group_plugin_policy 'group_file.so /etc/sudo-group' '%admins ALL=(ALL) NOPASSWD: /usr/bin/id'
  run ivan 'sudo -n /usr/bin/id -u'
  expect_rc 1; expect_out_empty
  end
}
begin group-plugin-always-query && {
  group_plugin_policy 'group_file.so /etc/sudo-group' $'Defaults always_query_group_plugin\n%admins ALL=(ALL) NOPASSWD: /usr/bin/id'
  run ivan 'sudo -n /usr/bin/id -u'
  expect_rc 0; expect_out_line 0
  end
}
begin group-plugin-always-query-numeric && {
  group_plugin_policy 'group_file.so /etc/sudo-group' $'Defaults always_query_group_plugin\n%#42003 ALL=(ALL) NOPASSWD: /usr/bin/id'
  run ivan 'sudo -n /usr/bin/id -u'
  expect_rc 0; expect_out_line 0
  end
}
begin group-plugin-always-query-preserves-unix && {
  group_plugin_policy 'group_file.so /etc/sudo-group' $'Defaults always_query_group_plugin\n%ivan ALL=(ALL) NOPASSWD: /usr/bin/id'
  run ivan 'sudo -n /usr/bin/id -u'
  expect_rc 0; expect_out_line 0
  end
}
begin group-plugin-missing-continues && {
  group_plugin_policy 'missing-group-plugin.so' 'ivan ALL=(ALL) NOPASSWD: /usr/bin/id'
  run ivan 'sudo -n /usr/bin/id -u'
  expect_rc 0; expect_out_line 0
  [[ $ERR == 'sudo: unable to load /usr/libexec/sudo/missing-group-plugin.so: /usr/libexec/sudo/missing-group-plugin.so: cannot open shared object file: No such file or directory' ]] || fail "unexpected loader diagnostic: $ERR"
  end
}
begin group-plugin-missing-no-membership && {
  group_plugin_policy 'missing-group-plugin.so' '%:admins ALL=(ALL) NOPASSWD: /usr/bin/id'
  run ivan 'sudo -n /usr/bin/id -u'
  expect_rc 1; expect_out_empty
  expect_err_has 'sudo: unable to load /usr/libexec/sudo/missing-group-plugin.so:'
  end
}
begin group-plugin-symbol-missing && {
  local_libc="/lib/$(uname -m)-linux-gnu/libc.so.6"
  group_plugin_policy "$local_libc" 'ivan ALL=(ALL) NOPASSWD: /usr/bin/id'
  run ivan 'sudo -n /usr/bin/id -u'
  expect_rc 0; expect_out_line 0
  [[ $ERR == "sudo: unable to find symbol \"group_plugin\" in $local_libc" ]] || fail "unexpected symbol diagnostic: $ERR"
  end
}
begin group-plugin-init-missing-argument && {
  group_plugin_policy 'group_file.so' 'ivan ALL=(ALL) NOPASSWD: /usr/bin/id'
  run ivan 'sudo -n /usr/bin/id -u'
  expect_rc 0; expect_out_line 0
  [[ $ERR == 'group_file: path to group file not specified' ]] || fail "unexpected init diagnostic: $ERR"
  end
}
begin group-plugin-init-unsafe-file && {
  group_plugin_policy 'group_file.so /etc/sudo-group' 'ivan ALL=(ALL) NOPASSWD: /usr/bin/id'
  chmod 0666 /etc/sudo-group
  run ivan 'sudo -n /usr/bin/id -u'
  expect_rc 0; expect_out_line 0
  [[ $ERR == '/etc/sudo-group must be only be writable by owner' ]] || fail "unexpected init diagnostic: $ERR"
  chmod 0644 /etc/sudo-group
  end
}
begin group-plugin-defaults-user && {
  group_plugin_policy 'group_file.so /etc/sudo-group' $'Defaults:%:admins !authenticate\n%:admins ALL=(ALL) /usr/bin/id'
  run ivan 'sudo -n /usr/bin/id -u'
  expect_rc 0; expect_out_line 0
  end
}

begin group-plugin-init-missing-file && {
  group_plugin_policy 'group_file.so /etc/sudo-group-missing' 'ivan ALL=(ALL) NOPASSWD: /usr/bin/id'
  run ivan 'sudo -n /usr/bin/id -u'
  expect_rc 0; expect_out_line 0
  expect_err_has 'group_file: /etc/sudo-group-missing: No such file or directory'
  end
}
begin group-plugin-file-gid-is-not-name && {
  group_plugin_policy 'group_file.so /etc/sudo-group' '%:#42001 ALL=(ALL) NOPASSWD: /usr/bin/id'
  run ivan 'sudo -n /usr/bin/id -u'
  expect_rc 1; expect_out_empty
  end
}
begin group-plugin-system-primary-not-member && {
  group_plugin_policy 'system_group.so' '%:ivan ALL=(ALL) NOPASSWD: /usr/bin/id'
  run ivan 'sudo -n /usr/bin/id -u'
  expect_rc 1; expect_out_empty
  end
}
begin group-plugin-file-user-case && {
  group_plugin_policy 'group_file.so /etc/sudo-group' '%:admins ALL=(ALL) NOPASSWD: /usr/bin/id'
  printf 'admins:x:42001:IVAN\n' >/etc/sudo-group
  run ivan 'sudo -n /usr/bin/id -u'
  expect_rc 0; expect_out_line 0
  end
}
begin group-plugin-unconfigured-no-unix-fallback && {
  printf '%%:ivan ALL=(ALL) NOPASSWD: /usr/bin/id\n' >/etc/sudoers.d/group-plugin
  chmod 0440 /etc/sudoers.d/group-plugin
  run ivan 'sudo -n /usr/bin/id -u'
  expect_rc 1; expect_out_empty
  end
}
begin group-plugin-list && {
  group_plugin_policy 'group_file.so /etc/sudo-group' '%:admins ALL=(ALL) NOPASSWD: /usr/bin/id'
  run ivan 'sudo -n -l'
  expect_rc 0; expect_out_has '(ALL) NOPASSWD: /usr/bin/id'
  end
}
begin group-plugin-list-other && {
  group_plugin_policy 'group_file.so /etc/sudo-group' '%:admins ALL=(ALL) NOPASSWD: /usr/bin/id'
  run root 'sudo -n -l -U ivan'
  expect_rc 0; expect_out_has '(ALL) NOPASSWD: /usr/bin/id'
  end
}

begin group-plugin-incompatible-version && {
  # Corrupt only the exported ABI version in the real shipped provider. Locate
  # the field through the loader mapping, so this works on either Docker arch.
  python3 - <<'PY'
import ctypes
from pathlib import Path
source = '/usr/libexec/sudo/group_file.so'
library = ctypes.CDLL(source)
address = ctypes.addressof(ctypes.c_uint.in_dll(library, 'group_plugin'))
for line in Path('/proc/self/maps').read_text().splitlines():
    fields = line.split()
    start, stop = (int(value, 16) for value in fields[0].split('-'))
    if start <= address < stop:
        offset = address - start + int(fields[2], 16)
        break
data = bytearray(Path(source).read_bytes())
data[offset:offset + 4] = bytes(ctypes.c_uint(2 << 16))
Path('/usr/libexec/sudo/group_bad_version.so').write_bytes(data)
PY
  group_plugin_policy 'group_bad_version.so' 'ivan ALL=(ALL) NOPASSWD: /usr/bin/id'
  run ivan 'sudo -n /usr/bin/id -u'
  expect_rc 0; expect_out_line 0
  [[ $ERR == 'sudo: /usr/libexec/sudo/group_bad_version.so: incompatible group plugin major version 2, expected 1' ]] || fail "unexpected version diagnostic: $ERR"
  rm -f /usr/libexec/sudo/group_bad_version.so
  end
}
