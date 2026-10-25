# Real LDAP -> SSSD sudo responder -> libsss_sudo integration, with no network
# beyond loopback. Run reference first: integration/run.sh reference '^sssd-'.
# Each case owns fresh slapd data, SSSD caches and services; no systemd required.
# Expectations come from sudo.ws 1.9.17p2 sssd.c / ldap_util.c / lookup.c and
# sudo_nss.c. Output (including LDAP role names in -ll) is compared with the
# installed reference, byte-for-byte; it is never synthesized as files output.

sssd_stop() {
  local pid=$1 i
  [[ -n $pid ]] || return 0
  kill -TERM -- "-$pid" 2>/dev/null || true
  for ((i=0; i<50; i++)); do
    kill -0 "$pid" 2>/dev/null || break
    sleep .1
  done
  kill -KILL -- "-$pid" 2>/dev/null || true
  wait "$pid" 2>/dev/null || true
}

sssd_cleanup() {
  [[ -n ${SSSD_DIR:-} ]] || return 0
  sssd_stop "${SSSD_PID:-}"
  sssd_stop "${SSSD_LDAP_PID:-}"
  SSSD_PID= SSSD_LDAP_PID=
  # Keep service diagnostics in the harness log even on a setup failure.
  local f
  for f in "$SSSD_DIR"/*.log; do
    [[ -f $f ]] || continue
    printf '\n--- %s\n' "${f##*/}" >>"$LOG"
    cat "$f" >>"$LOG"
  done
  if [[ -f $SSSD_DIR/nsswitch.orig ]]; then
    cp -a "$SSSD_DIR/nsswitch.orig" /etc/nsswitch.conf
  fi
  if [[ -d $SSSD_DIR/etc-sssd.orig ]]; then
    rm -rf /etc/sssd
    mv "$SSSD_DIR/etc-sssd.orig" /etc/sssd
  fi
  if [[ -d $SSSD_DIR/lib-sss.orig ]]; then
    rm -rf /var/lib/sss
    mv "$SSSD_DIR/lib-sss.orig" /var/lib/sss
  fi
  if [[ -f $SSSD_DIR/sudoers.orig ]]; then
    cp -a "$SSSD_DIR/sudoers.orig" /etc/sudoers
  fi
  rm -rf "$SSSD_DIR"
  SSSD_DIR=
  trap - EXIT
  [[ -z ${SSSD_EXIT_TRAP:-} ]] || eval "$SSSD_EXIT_TRAP"
}

sssd_nss() {
  sed '/^[[:blank:]]*sudoers:/Id' "$SSSD_DIR/nsswitch.orig" >/etc/nsswitch.conf
  printf '\nsudoers: %s\n' "$1" >>/etc/nsswitch.conf
}

sssd_role() {
  local name=$1
  shift
  printf '\ndn: cn=%s,ou=SUDOers,dc=sudo,dc=test\nobjectClass: sudoRole\ncn: %s\n' "$name" "$name" >>"$SSSD_DIR/entries.ldif"
  printf '%s\n' "$@" >>"$SSSD_DIR/entries.ldif"
}

sssd_fixture() {
  local scenario=$1 auth='!authenticate'
  case $scenario in role-noauth|role-auth-scope|auth-required) auth=authenticate;; esac
  cat >"$SSSD_DIR/entries.ldif" <<EOF
dn: dc=sudo,dc=test
objectClass: domain
dc: sudo

dn: ou=People,dc=sudo,dc=test
objectClass: organizationalUnit
ou: People

dn: ou=Groups,dc=sudo,dc=test
objectClass: organizationalUnit
ou: Groups

dn: ou=SUDOers,dc=sudo,dc=test
objectClass: organizationalUnit
ou: SUDOers

dn: uid=ivan,ou=People,dc=sudo,dc=test
objectClass: account
objectClass: posixAccount
cn: ivan
uid: ivan
uidNumber: $(uid_of ivan)
gidNumber: $(gid_of ivan)
homeDirectory: /home/ivan
loginShell: /bin/bash

dn: cn=ivan,ou=Groups,dc=sudo,dc=test
objectClass: posixGroup
cn: ivan
gidNumber: $(gid_of ivan)
memberUid: ivan
EOF
  sssd_role defaults 'sudoOption: lecture=never' 'sudoOption: passwd_tries=1' "sudoOption: $auth"
  # A separate command is a positive end-to-end readiness probe, including for
  # negative cases: an unavailable server must not make a denial test pass.
  sssd_role ready 'sudoUser: ivan' 'sudoHost: ALL' 'sudoCommand: /usr/bin/true' \
    'sudoRunAsUser: root' 'sudoOption: !authenticate' 'sudoOrder: 1'
  local users='sudoUser: ivan' hosts='sudoHost: ALL' commands='sudoCommand: /usr/bin/id' runas='sudoRunAsUser: root'
  local options='sudoOption: !authenticate' order=20
  case $scenario in
    deny|nss-notfound-return|nss-notfound-continue) commands='sudoCommand: /usr/bin/printf';;
    command-negation) commands=$'sudoCommand: /usr/bin/id\nsudoCommand: !/usr/bin/id';;
    # Measured sudo.ws 1.9.17p2 + SSSD 2.12.0 allows this mixed rule.
    # Do not impose files-style negation precedence on SSSD's returned values:
    # sudo_sss_check_user stops walking values at its first positive match.
    user-negation) users=$'sudoUser: !ivan\nsudoUser: ALL';;
    host-negation) hosts=$(printf 'sudoHost: ALL\nsudoHost: !%s' "$host");;
    runas-negation) runas=$'sudoRunAsUser: ALL\nsudoRunAsUser: !root';;
    runas-user) runas='sudoRunAsUser: bob';;
    runas-group) runas=$'sudoRunAsUser: bob\nsudoRunAsGroup: root';;
    runas-group-negation) runas=$'sudoRunAsUser: bob\nsudoRunAsGroup: ALL\nsudoRunAsGroup: !root';;
    global-noauth|auth-required) options='sudoOption: env_reset';;
    role-runas-default)
      runas=
      options=$'sudoOption: !authenticate\nsudoOption: runas_default=ivan';;
    role-runchroot|role-runchroot-cwd)
      commands='sudoCommand: /usr/bin/jail-tool'
      options=$'sudoOption: !authenticate\nsudoOption: runchroot=/srv/lean-sudo-jail'
      [[ $scenario != role-runchroot-cwd ]] || options+=$'\nsudoOption: runcwd=/work';;
    wildcard-command-args)
      commands=$'sudoCommand: /usr/bin/* -[ug]\nsudoCommand: !/usr/bin/print* *';;
    order-deny|nss-files-sss|nss-sss-files|nss-files-success-return|nss-sss-success-return)
      commands='sudoCommand: !/usr/bin/id'; order=200;;
    order-allow) order=200;;
    order-negative) order=-10;;
    list-short|list-long|list-short-success-return|list-long-success-return)
      commands=$'sudoCommand: /usr/bin/id\nsudoCommand: !/usr/bin/id -u'
      runas=$'sudoRunAsUser: root\nsudoRunAsUser: bob\nsudoRunAsGroup: root'
      options=$'sudoOption: !authenticate\nsudoOption: env_keep+=SSSD_LIST\nsudoOption: !setenv';;
  esac
  local attrs=("$users" "$hosts" "$commands")
  [[ -z $runas ]] || attrs+=("$runas")
  sssd_role ldap-policy "${attrs[@]}" "$options" "sudoOrder: $order"
  case $scenario in
    order-deny)
      # Insert the lower-order role LAST, deliberately opposing insertion order.
      sssd_role lower-order 'sudoUser: ivan' 'sudoHost: ALL' 'sudoCommand: /usr/bin/id' 'sudoOrder: 10';;
    order-allow)
      sssd_role lower-order 'sudoUser: ivan' 'sudoHost: ALL' 'sudoCommand: !/usr/bin/id' 'sudoOrder: 10';;
    order-negative)
      # Upstream's LDAP schema permits signed integer sudoOrder values. A
      # larger negative order must win, independent of LDAP insertion order.
      sssd_role lower-order 'sudoUser: ivan' 'sudoHost: ALL' 'sudoCommand: !/usr/bin/id' 'sudoOrder: -20';;
    role-auth-scope)
      sssd_role requires-password 'sudoUser: ivan' 'sudoHost: ALL' 'sudoCommand: /usr/bin/printf' 'sudoOrder: 30';;
    list-short|list-long|list-short-success-return|list-long-success-return)
      sssd_role second-role 'sudoUser: ivan' 'sudoHost: ALL' 'sudoCommand: /usr/bin/printf' 'sudoRunAsUser: bob' 'sudoOption: authenticate' 'sudoOrder: 30';;
  esac
}

sssd_setup() {
  local scenario=$1 i CMD_TIMEOUT=3
  # Do not stop or overwrite an unrelated daemon. The integration image starts
  # no services; both processes below are foreground children in owned groups.
  if pgrep -x sssd >/dev/null || pgrep -x slapd >/dev/null; then
    fail 'SSSD fixture requires the throwaway container with sssd/slapd stopped'
    return 1
  fi
  SSSD_DIR=$(mktemp -d "$WORK/sssd.XXXXXX")
  chmod 0755 "$SSSD_DIR"
  SSSD_PID= SSSD_LDAP_PID=
  SSSD_EXIT_TRAP=$(trap -p EXIT)
  trap sssd_cleanup EXIT
  cp -a /etc/nsswitch.conf "$SSSD_DIR/nsswitch.orig" || return 1
  cp -a /etc/sudoers "$SSSD_DIR/sudoers.orig" || return 1
  mkdir -p /etc/sssd /var/lib/sss
  mv /etc/sssd "$SSSD_DIR/etc-sssd.orig" || return 1
  mv /var/lib/sss "$SSSD_DIR/lib-sss.orig" || return 1
  # Preserve package-created ownership/modes (including non-root SSSD builds),
  # but never reuse the original cache or a previous case's cached rules.
  cp -a "$SSSD_DIR/lib-sss.orig" /var/lib/sss || return 1
  rm -rf /var/lib/sss/db/* /var/lib/sss/mc/* /var/lib/sss/pipes/*
  mkdir -p /etc/sssd/conf.d /var/lib/sss/db /var/lib/sss/mc \
    /var/lib/sss/pipes/private /var/lib/sss/pubconf /var/log/sssd /run/sssd
  chmod 0770 /var/lib/sss/pipes/private
  chown --reference=/var/lib/sss/pipes /var/lib/sss/pipes/private
  mkdir -p "$SSSD_DIR/config" "$SSSD_DIR/data"
  cat >"$SSSD_DIR/slapd.conf" <<EOF
include /etc/ldap/schema/core.schema
include /etc/ldap/schema/cosine.schema
include /etc/ldap/schema/nis.schema
pidfile $SSSD_DIR/slapd.pid
argsfile $SSSD_DIR/slapd.args
modulepath /usr/lib/ldap
moduleload back_mdb
database mdb
maxsize 1073741824
suffix "dc=sudo,dc=test"
rootdn "cn=admin,dc=sudo,dc=test"
rootpw fixture-password
directory $SSSD_DIR/data
index objectClass eq
access to * by * read
EOF
  # Generate isolated cn=config, then load the vendored schema offline.
  slapcat -n 0 -f "$SSSD_DIR/slapd.conf" -F "$SSSD_DIR/config" -l "$SSSD_DIR/config.ldif" >"$SSSD_DIR/schema.log" 2>&1 || return 1
  slapadd -n 0 -F "$SSSD_DIR/config" -l /opt/sudo-it/sudo-schema.ldif >>"$SSSD_DIR/schema.log" 2>&1 || return 1
  sssd_fixture "$scenario"
  setsid slapd -F "$SSSD_DIR/config" -h ldap://127.0.0.1:1389/ -d 0 >"$SSSD_DIR/slapd.log" 2>&1 &
  SSSD_LDAP_PID=$!
  for ((i=0; i<100; i++)); do
    ldapwhoami -x -H ldap://127.0.0.1:1389 -o nettimeout=1 -D cn=admin,dc=sudo,dc=test -w fixture-password >/dev/null 2>&1 && break
    kill -0 "$SSSD_LDAP_PID" 2>/dev/null || return 1
    sleep .1
  done
  ldapadd -x -H ldap://127.0.0.1:1389 -D cn=admin,dc=sudo,dc=test -w fixture-password -f "$SSSD_DIR/entries.ldif" >"$SSSD_DIR/ldapadd.log" 2>&1 || return 1
  cat >/etc/sssd/sssd.conf <<'EOF'
[sssd]
services = nss, sudo
domains = sudo.test

[nss]

[sudo]

[domain/sudo.test]
id_provider = ldap
auth_provider = none
access_provider = permit
sudo_provider = ldap
ldap_uri = ldap://127.0.0.1:1389
ldap_search_base = dc=sudo,dc=test
ldap_user_search_base = ou=People,dc=sudo,dc=test
ldap_group_search_base = ou=Groups,dc=sudo,dc=test
ldap_sudo_search_base = ou=SUDOers,dc=sudo,dc=test
ldap_schema = rfc2307
ldap_id_use_start_tls = false
ldap_sudo_use_host_filter = false
ldap_sudo_smart_refresh_interval = 0
ldap_sudo_full_refresh_interval = 3600
use_fully_qualified_names = false
cache_credentials = false
enumerate = false
min_id = 1
EOF
  chmod 0600 /etc/sssd/sssd.conf
  # Do not include the stock sudoers.d grants. Identity still resolves from the
  # existing local account; SSSD independently finds its matching LDAP UID/GID.
  printf 'Defaults !authenticate, lecture=never\n' >/etc/sudoers
  chmod 0440 /etc/sudoers
  sssd_nss sss
  # Ubuntu's service unit requires SupplementaryGroups=sssd when running the
  # monitor as root: SSSD drops DAC capabilities before opening its sockets.
  # Keep package sssd:sssd ownership and private group-only directory access.
  setsid setpriv --groups=sssd -- sssd -i --logger=stderr >"$SSSD_DIR/sssd.log" 2>&1 &
  SSSD_PID=$!
  for ((i=0; i<50; i++)); do
    run ivan '/usr/bin/sudo.ws -n /usr/bin/true'
    [[ $RC != 0 ]] || return 0
    kill -0 "$SSSD_PID" 2>/dev/null || return 1
    sleep .1
  done
  return 1
}

sssd_compare() {
  local args=$1 expected=$2 ref_rc
  rm -rf /run/sudo
  run ivan "/usr/bin/sudo.ws $args"
  ref_rc=$RC
  expect_rc "$expected"
  cp "$WORK/out" "$SSSD_DIR/reference.out"
  sed 's/sudo\.ws/sudo/g' "$WORK/err" >"$SSSD_DIR/reference.err"
  rm -rf /run/sudo
  run ivan "/usr/bin/sudo $args"
  expect_rc "$ref_rc"
  diff -u "$SSSD_DIR/reference.out" "$WORK/out" >>"$LOG" || fail 'SSSD stdout differs from sudo.ws (see diff in log)'
  sed 's/sudo\.ws/sudo/g' "$WORK/err" >"$SSSD_DIR/actual.err"
  diff -u "$SSSD_DIR/reference.err" "$SSSD_DIR/actual.err" >>"$LOG" || fail 'SSSD stderr differs from sudo.ws (see diff in log)'
}

for sssd_case in allow deny command-negation user-negation host-negation runas-negation \
    runas-user runas-group runas-group-negation order-allow order-deny order-negative \
    role-noauth role-auth-scope role-runas-default role-runchroot role-runchroot-cwd global-noauth auth-required \
    wildcard-command-args list-short list-long list-short-success-return list-long-success-return \
    nss-files-sss nss-sss-files nss-notfound-return nss-notfound-continue \
    nss-files-success-return nss-sss-success-return; do
  begin "sssd-$sssd_case" && {
    if sssd_setup "$sssd_case"; then
      sssd_args='-n /usr/bin/id -u'
      sssd_expected=0
      case $sssd_case in
        deny|command-negation|host-negation|runas-negation|order-deny|auth-required)
          sssd_expected=1;;
        runas-user) sssd_args='-n -u bob /usr/bin/id -u';;
        runas-group) sssd_args='-n -u bob -g root /usr/bin/id -g';;
        runas-group-negation) sssd_args='-n -u bob -g root /usr/bin/id -g'; sssd_expected=1;;
        role-runchroot|role-runchroot-cwd)
          exec_chroot_setup
          sssd_args='-n /usr/bin/jail-tool';;
        list-short) sssd_args='-n -l';;
        list-long) sssd_args='-n -ll';;
        list-short-success-return|list-long-success-return)
          printf 'ivan ALL=(root) NOPASSWD: /usr/bin/id\n' >>/etc/sudoers
          sssd_nss 'files [SUCCESS=return] sss'
          sssd_args='-n -l'
          [[ $sssd_case != list-long-success-return ]] || sssd_args='-n -ll';;
        nss-*)
          printf 'ivan ALL=(root) NOPASSWD: /usr/bin/id\n' >>/etc/sudoers
          case $sssd_case in
            nss-files-sss) sssd_nss 'files sss'; sssd_expected=1;;
            nss-sss-files) sssd_nss 'sss files';;
            nss-notfound-return) sssd_nss 'sss [NOTFOUND=return] files'; sssd_expected=1;;
            nss-notfound-continue) sssd_nss 'sss files';;
            nss-files-success-return) sssd_nss 'files [SUCCESS=return] sss';;
            # sudo_nss.c defines SUCCESS as a specified match, including DENY.
            nss-sss-success-return) sssd_nss 'sss [SUCCESS=return] files'; sssd_expected=1;;
          esac;;
      esac
      sssd_compare "$sssd_args" "$sssd_expected"
      case $sssd_case in
        allow|user-negation|order-allow|order-negative|role-noauth|global-noauth|nss-sss-files|nss-notfound-continue|nss-files-success-return)
          expect_out_line 0;;
        runas-user) expect_out_line "$(uid_of bob)";;
        runas-group) expect_out_line 0;;
        role-runas-default)
          # Measured reference behavior: the rule matches with the initial
          # root default, then its option changes the execution target to ivan.
          expect_out_line "$(uid_of ivan)";;
        role-runchroot|role-runchroot-cwd)
          expect_out_line jail-marker
          expect_out_line 0
          if [[ $sssd_case == role-runchroot-cwd ]]; then expect_out_line cwd=/work
          else expect_out_line cwd=/; fi
          rm -rf /srv/lean-sudo-jail;;
        wildcard-command-args)
          expect_out_line 0
          sssd_compare '-n /usr/bin/id -un' 1
          expect_out_empty
          sssd_compare '-n /usr/bin/printf -u' 1
          expect_out_empty;;
        list-short-success-return)
          expect_out_has '!/usr/bin/id -u'
          expect_out_has '/usr/bin/printf';;
        list-long-success-return)
          expect_out_has 'ldap-policy'
          expect_out_has 'second-role';;
        role-auth-scope)
          expect_out_line 0
          sssd_compare '-n /usr/bin/printf should-not-run' 1
          expect_out_empty
          expect_err_has "$PW_REQUIRED";;
        auth-required) expect_err_has "$PW_REQUIRED";;
      esac
      [[ $sssd_expected != 1 ]] || expect_out_empty
    else
      fail 'real slapd/SSSD setup failed (see schema/ldapadd/service logs)'
    fi
    sssd_cleanup
    end
  }
done
