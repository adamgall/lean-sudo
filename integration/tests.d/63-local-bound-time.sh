




local_bound_cleanup() {
  [[ -n ${LOCAL_BOUND_DIR:-} ]] || return 0
  if [[ ${LOCAL_BOUND_CHANGED:-0} == 1 ]]; then
    rm -f /etc/localtime || { fail 'Cannot remove local-bound timezone'; return 1; }
    if [[ -e $LOCAL_BOUND_DIR/localtime || -L $LOCAL_BOUND_DIR/localtime ]]; then
      cp -a "$LOCAL_BOUND_DIR/localtime" /etc/localtime || {
        fail "Cannot restore system timezone from $LOCAL_BOUND_DIR/localtime"
        return 1
      }
    fi
    LOCAL_BOUND_CHANGED=0
  fi
  rm -rf "$LOCAL_BOUND_DIR"
  LOCAL_BOUND_DIR=
  trap - EXIT HUP INT TERM
  [[ -z ${LOCAL_BOUND_TRAPS:-} ]] || eval "$LOCAL_BOUND_TRAPS"
}

local_bound_setup() {
  LOCAL_BOUND_DIR=$(mktemp -d "$WORK/local-bound.XXXXXX") || {
    fail 'Cannot create local-bound fixture directory'
    return 1
  }
  LOCAL_BOUND_CHANGED=0
  LOCAL_BOUND_TRAPS=$(trap -p EXIT HUP INT TERM)
  trap local_bound_cleanup EXIT
  trap 'exit 129' HUP
  trap 'exit 130' INT
  trap 'exit 143' TERM
  [[ -f /usr/share/zoneinfo/America/New_York ]] || {
    fail 'America/New_York zoneinfo is required'
    return 1
  }


  if [[ -e /etc/localtime || -L /etc/localtime ]]; then
    cp -a /etc/localtime "$LOCAL_BOUND_DIR/localtime" || {
      fail 'Cannot save system timezone'
      return 1
    }
  fi
  LOCAL_BOUND_CHANGED=1
  rm -f /etc/localtime && ln -s /usr/share/zoneinfo/America/New_York /etc/localtime || {
    fail 'Cannot install America/New_York system timezone'
    return 1
  }
}




local_bound_compare() {
  local user=$1 command=$2 status=$3
  run "$user" 'sudo() { /bin/bash -c '\''exec -a sudo /usr/bin/sudo.ws "$@"'\'' -- "$@"; }; '"$command"
  expect_rc "$status"
  cp "$WORK/out" "$LOCAL_BOUND_DIR/reference-out"
  cp "$WORK/err" "$LOCAL_BOUND_DIR/reference-err"
  run "$user" "$command"
  expect_rc "$status"
  diff -u "$LOCAL_BOUND_DIR/reference-out" "$WORK/out" >>"$LOG" || fail 'stdout differs from sudo.ws'
  diff -u "$LOCAL_BOUND_DIR/reference-err" "$WORK/err" >>"$LOG" || fail 'stderr differs from sudo.ws'
}

local_bound_listing() {
  local scenario=$1 mode=$2 before after expected_before expected_after option
  case $scenario in
    winter)
      before=20240115120000 expected_before=20240115170000Z ;;
    summer)
      before=20240715120000 expected_before=20240715160000Z ;;
    spring-gap)

      before=20240310023000 expected_before=20240310073000Z ;;
    fall-fold)
      before=20241103013000


      expected_before=$(env -u TZ python3 -c 'import time; time.tzset(); epoch = time.mktime((2024, 11, 3, 1, 30, 0, 0, 0, -1)); print(time.strftime("%Y%m%d%H%M%SZ", time.gmtime(epoch)))') || {
        fail 'Cannot resolve fold with system-zone mktime'
        return 1
      } ;;
    explicit-z)
      before=20240310023000Z expected_before=20240310023000Z ;;
    explicit-offset)
      before=20240310023000+0530 expected_before=20240309210000Z ;;
    caller-TZ)
      before=20240115120000 expected_before=20240115170000Z

      XENV=(TZ=UTC+12) ;;
  esac
  after=$before expected_after=$expected_before
  if [[ $scenario == caller-TZ ]]; then
    after=20240715120000 expected_after=20240715160000Z
  fi
  printf 'pete ALL = (root) NOTBEFORE=%s NOTAFTER=%s NOPASSWD: /usr/bin/id\n' \
    "$before" "$after" | install -m 0440 /dev/stdin /etc/sudoers.d/local-bound-time
  if [[ $mode == short ]]; then option=-l; else option=-ll; fi


  local_bound_compare root "sudo -n $option -U pete" 0
  if [[ $mode == short ]]; then
    expect_out_line "    (root) NOTBEFORE=$expected_before NOTAFTER=$expected_after NOPASSWD:"
    expect_out_line "        /usr/bin/id"
  else
    expect_out_line "    NotBefore: $expected_before"
    expect_out_line "    NotAfter: $expected_after"
  fi
}



for local_bound_case in winter summer spring-gap fall-fold explicit-z explicit-offset caller-TZ; do
  for local_bound_mode in short long; do
    begin "local-bound-$local_bound_case-list-$local_bound_mode" && {
      if local_bound_setup; then
        local_bound_listing "$local_bound_case" "$local_bound_mode"
      fi
      local_bound_cleanup
      end
    }
  done
done

local_bound_live() {
  local scenario=$1 bound value status
  case $scenario in
    past-notbefore-allow) bound=NOTBEFORE; value='2 days ago'; status=0 ;;
    future-notafter-allow) bound=NOTAFTER; value='+2 days'; status=0 ;;
    future-notbefore-deny) bound=NOTBEFORE; value='+2 days'; status=1 ;;
    past-notafter-deny) bound=NOTAFTER; value='2 days ago'; status=1 ;;
  esac

  value=$(env -u TZ date -d "$value" +%Y%m%d%H%M%S) || {
    fail 'Cannot generate system-local live bound'
    return 1
  }
  install -m 0440 /dev/stdin /etc/sudoers.d/local-bound-time <<EOF
Defaults:pete !authenticate
pete ALL = (root) NOPASSWD: /usr/bin/true
pete ALL = (root) $bound=$value NOPASSWD: /usr/bin/id
EOF

  local_bound_compare pete 'sudo -n /usr/bin/true' 0
  expect_out_empty
  local_bound_compare pete 'sudo -n /usr/bin/id -u' "$status"
  if [[ $status == 0 ]]; then expect_out_line 0; else expect_out_empty; fi
}

for local_bound_case in past-notbefore-allow future-notafter-allow future-notbefore-deny past-notafter-deny; do
  begin "local-bound-$local_bound_case" && {
    if local_bound_setup; then
      local_bound_live "$local_bound_case"
    fi
    local_bound_cleanup
    end
  }
done
