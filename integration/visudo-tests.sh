#!/bin/bash








set -u

VISUDO=${1:?usage: visudo-tests.sh VISUDO_BINARY [NAME_FILTER]}
FILTER=${2:-}
LABEL=${IMPL_LABEL:-$(basename "$VISUDO")}
OUTDIR=${OUTDIR:-/out}
WORK=$(mktemp -d /tmp/visudo-it.XXXXXX)
chmod 0755 "$WORK"
REFERENCE=/usr/sbin/visudo.ws
CMD_TIMEOUT=40
IS_REF=0
[[ $VISUDO == "$REFERENCE" ]] && IS_REF=1
SUDO=${VISUDO_SUDO_BINARY:-/usr/bin/sudo.ws}

[[ -f $VISUDO ]] || { echo "Bail out! $VISUDO does not exist"; exit 2; }
chmod 0755 "$VISUDO"

cp -a /etc/sudoers "$WORK/sudoers.orig"
cp -a /etc/sudoers.d "$WORK/sudoers.d.orig"


ED=$WORK/ed
mkdir -p "$ED"
cat >"$ED/append" <<'EOF'
#!/bin/sh

for a; do f=$a; done
printf '%s\n' "$*" >>"${EDLOG:-/dev/null}"
printf '%s\n' "$LINE" >>"$f"
EOF
cat >"$ED/noop" <<'EOF'
#!/bin/sh
printf '%s\n' "$*" >>"${EDLOG:-/dev/null}"
EOF
cat >"$ED/empty" <<'EOF'
#!/bin/sh
for a; do f=$a; done
: >"$f"
EOF
cat >"$ED/wait" <<'EOF'
#!/bin/sh

: >"$STARTED"
i=0
while [ ! -e "$RELEASE" ] && [ $i -lt 200 ]; do sleep 0.1; i=$((i + 1)); done
EOF
chmod 0755 "$ED"/*

mkdir -p "$OUTDIR"
LOG="$OUTDIR/$LABEL.log"
TAP="$OUTDIR/$LABEL.tap"
: >"$LOG"
: >"$TAP"
if [[ -n ${HOST_UID:-} ]]; then chown "$HOST_UID:${HOST_GID:-$HOST_UID}" "$LOG" "$TAP"; fi

reset_state() {
  rm -rf /etc/sudoers.d /etc/sudoers.tmp "$WORK"/scratch
  cp -a "$WORK/sudoers.d.orig" /etc/sudoers.d
  cp -a "$WORK/sudoers.orig" /etc/sudoers
  chown root:root /etc/sudoers; chmod 0440 /etc/sudoers
  mkdir -p "$WORK/scratch"
  : >"$WORK/edlog"
}





NUM=0 PASSED=0 FAILED=0 SKIPPED=0
FAILED_NAMES=()
CUR= CMD= RC= OUT= ERR=
FAILS=()
XENV=()
STDIN=/dev/null

emit() { printf '%s\n' "$*" | tee -a "$TAP" "$LOG"; }

begin() {
  CUR=$1
  if [[ -n $FILTER ]] && ! [[ $CUR =~ $FILTER ]]; then return 1; fi
  FAILS=() XENV=() CMD= RC= OUT= ERR= STDIN=/dev/null
  reset_state
  printf '\n=== %s\n' "$CUR" >>"$LOG"
  return 0
}




vrun() {
  local user=root
  if [[ ${1:-} == -u ]]; then user=$2; shift 2; fi
  CMD="visudo $*"
  local pre=()
  [[ $user != root ]] && pre=(setpriv --reuid="$user" --regid="$(id -g "$user")" --init-groups --)
  env -i HOME=/root PATH=/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin \
      LANG=C.UTF-8 EDLOG="$WORK/edlog" "${XENV[@]}" \
    timeout -k 5 "$CMD_TIMEOUT" "${pre[@]}" "$VISUDO" "$@" \
    >"$WORK/out" 2>"$WORK/err" <"$STDIN"
  RC=$?
  OUT=$(cat "$WORK/out")
  ERR=$(cat "$WORK/err")
  {
    printf -- '--- run as %s: %s\n' "$user" "$CMD"
    [[ ${#XENV[@]} -gt 0 ]] && printf -- '--- extra env: %s\n' "${XENV[*]}"
    [[ $STDIN != /dev/null ]] && printf -- '--- stdin: %s\n' "$(cat "$STDIN")"
    printf -- '--- rc=%s\n--- stdout:\n%s\n--- stderr:\n%s\n' "$RC" "$OUT" "$ERR"
  } >>"$LOG"
}


answer() { printf '%s' "$1" >"$WORK/stdin"; STDIN=$WORK/stdin; }

fail() { FAILS+=("$1"); }
expect_rc() { [[ $RC == "$1" ]] || fail "exit status: expected $1, got $RC"; }
expect_out_line() { grep -qxF -- "$1" <<<"$OUT" || fail "stdout: expected a line equal to '$1'"; }
expect_out_has() { grep -qF -- "$1" <<<"$OUT" || fail "stdout: expected to contain '$1'"; }
expect_out_lacks() { ! grep -qF -- "$1" <<<"$OUT" || fail "stdout: expected NOT to contain '$1'"; }
expect_out_empty() { [[ -z $OUT ]] || fail "stdout: expected empty"; }
expect_out_exactly() { [[ $OUT == "$1" ]] || fail "stdout: expected exactly:"$'\n'"$1"; }
expect_err_has() { grep -qF -- "$1" <<<"$ERR" || fail "stderr: expected to contain '$1'"; }
expect_err_match() { grep -qE -- "$1" <<<"$ERR" || fail "stderr: expected to match /$1/"; }
expect_err_empty() { [[ -z $ERR ]] || fail "stderr: expected empty"; }

expect_stat() {
  local got
  got=$(stat -c '%a %U %G' "$1" 2>&1)
  [[ $got == "$2" ]] || fail "$1: expected '$2', got '$got'"
}
expect_unchanged() {
  cmp -s /etc/sudoers "$WORK/sudoers.orig" || fail "/etc/sudoers was modified"
  expect_stat /etc/sudoers '440 root root'
}
expect_no_tmp() { [[ ! -e ${1:-/etc/sudoers.tmp} ]] || fail "${1:-/etc/sudoers.tmp} left behind"; }
expect_last_line() {
  local got
  got=$(tail -n 1 "$1")
  [[ $got == "$2" ]] || fail "$1: expected last line '$2', got '$got'"
}

indent() { sed 's/^/#     /'; }

end() {
  NUM=$((NUM + 1))
  if [[ ${#FAILS[@]} -eq 0 ]]; then
    PASSED=$((PASSED + 1))
    emit "ok $NUM - $CUR"
  else
    FAILED=$((FAILED + 1))
    FAILED_NAMES+=("$CUR")
    emit "not ok $NUM - $CUR"
    {
      local f
      for f in "${FAILS[@]}"; do printf '#   %s\n' "$f"; done
      printf '#   command: %s\n' "$CMD"
      [[ ${#XENV[@]} -gt 0 ]] && printf '#   extra env: %s\n' "${XENV[*]}"
      printf '#   exit status: %s\n' "$RC"
      printf '#   stdout:\n'; printf '%s\n' "$OUT" | indent
      printf '#   stderr:\n'; printf '%s\n' "$ERR" | indent
    } | tee -a "$TAP" "$LOG"
  fi
}



STOCK_OK=$(
  printf '/etc/sudoers: parsed OK\n'
  for file in /etc/sudoers.d/*; do
    case "${file##*/}" in *.*|*~) continue ;; esac
    [[ -f $file ]] && printf '%s: parsed OK\n' "$file"
  done
)
SYNTAX_LINE=$(($(wc -l </etc/sudoers) + 1))





begin check-stock && {
  vrun -c
  expect_rc 0
  expect_out_exactly "$STOCK_OK"
  expect_err_empty
  end
}

begin check-stock-explicit-file && {
  vrun -c -f /etc/sudoers
  expect_rc 0
  expect_out_exactly "$STOCK_OK"
  end
}

begin check-stock-operand-and-long-options && {
  vrun --check /etc/sudoers
  expect_rc 0
  expect_out_exactly "$STOCK_OK"
  end
}

begin check-quiet && {
  vrun -c -q
  expect_rc 0
  expect_out_empty
  expect_err_empty
  end
}

begin check-stdin && {
  printf 'root ALL=(ALL:ALL) ALL\n' >"$WORK/scratch/in"
  STDIN=$WORK/scratch/in
  vrun -c -f -
  expect_rc 0
  expect_out_exactly "stdin: parsed OK"
  end
}

begin check-syntax-error-main && {
  echo 'foo bar baz' >>/etc/sudoers
  vrun -c
  expect_rc 1
  expect_out_lacks 'parsed OK'
  expect_err_match "^/etc/sudoers:$SYNTAX_LINE:[0-9]+: syntax error"
  expect_err_has 'foo bar baz'
  end
}

begin check-syntax-error-include && {
  install -o root -g root -m 0440 /dev/null /etc/sudoers.d/zz-bad
  echo 'foo bar' >/etc/sudoers.d/zz-bad
  vrun -c
  expect_rc 1
  expect_out_lacks 'parsed OK'
  expect_err_match '^/etc/sudoers.d/zz-bad:1:[0-9]+: syntax error'
  end
}

begin check-syntax-error-quiet && {
  echo 'foo bar baz' >>/etc/sudoers
  vrun -c -q
  expect_rc 1
  expect_out_empty
  expect_err_empty
  end
}

begin check-bad-perms-main && {
  chmod 0644 /etc/sudoers
  vrun -c
  expect_rc 1
  expect_err_has '/etc/sudoers: bad permissions, should be mode 0440'
  expect_out_lacks '/etc/sudoers: parsed OK'
  expect_out_line '/etc/sudoers.d/carol: parsed OK'
  end
}

begin check-bad-owner-main && {
  chown bob:bob /etc/sudoers
  vrun -c
  expect_rc 1
  expect_err_has '/etc/sudoers: wrong owner (uid, gid) should be (0, 0)'
  expect_out_lacks '/etc/sudoers: parsed OK'
  end
}

begin check-bad-perms-include && {
  echo 'bob ALL=(ALL) ALL' >/etc/sudoers.d/zz
  chmod 0666 /etc/sudoers.d/zz
  vrun -c
  expect_rc 1
  expect_err_has '/etc/sudoers.d/zz: bad permissions, should be mode 0440'
  expect_out_line '/etc/sudoers: parsed OK'
  end
}

begin check-file-option-skips-owner-perms && {

  chmod 0644 /etc/sudoers
  vrun -c -f /etc/sudoers
  expect_rc 0
  expect_out_line '/etc/sudoers: parsed OK'
  end
}

begin check-file-option-with-P && {
  chmod 0644 /etc/sudoers
  vrun -c -P -f /etc/sudoers
  expect_rc 1
  expect_err_has '/etc/sudoers: bad permissions, should be mode 0440'
  end
}

begin check-file-option-with-O && {
  chown bob /etc/sudoers
  vrun -c -O -f /etc/sudoers
  expect_rc 1
  expect_err_has '/etc/sudoers: wrong owner (uid, gid) should be (0, 0)'
  end
}

begin check-missing-include && {
  printf 'root ALL=(ALL) ALL\n@include /nonexistent-file\n' >"$WORK/scratch/s"
  vrun -c -f "$WORK/scratch/s"
  expect_rc 1
  expect_err_has '/nonexistent-file'
  expect_out_lacks 'parsed OK'
  end
}

begin check-duplicate-alias && {
  printf 'User_Alias A = bob\nUser_Alias A = carol\nA ALL = ALL\n' >"$WORK/scratch/s"
  vrun -c -f "$WORK/scratch/s"
  expect_rc 1
  expect_err_has 'duplicate User_Alias "A"'
  end
}

begin check-unknown-defaults && {
  printf 'Defaults foobar\n' >"$WORK/scratch/s"
  vrun -c -f "$WORK/scratch/s"
  expect_rc 1
  expect_err_has 'unknown defaults entry "foobar"'
  end
}

begin check-invalid-defaults-value && {
  printf 'Defaults passwd_tries=abc\n' >"$WORK/scratch/s"
  vrun -c -f "$WORK/scratch/s"
  expect_rc 1
  expect_err_has 'value "abc" is invalid for option "passwd_tries"'
  end
}

begin check-undefined-alias-is-error && {

  printf 'bob FOO = /usr/bin/id\n' >"$WORK/scratch/s"
  vrun -c -s -f "$WORK/scratch/s"
  expect_rc 1
  expect_err_has 'Host_Alias "FOO" referenced but not defined'
  end
}





begin edit-append-valid-line && {
  chmod 0640 /etc/sudoers
  XENV=(EDITOR="$ED/append" LINE='bob ALL=(ALL) /usr/bin/id')
  vrun
  expect_rc 0
  expect_last_line /etc/sudoers 'bob ALL=(ALL) /usr/bin/id'
  expect_stat /etc/sudoers '440 root root'
  expect_no_tmp
  [[ $(head -n 1 "$WORK/edlog") == *"/etc/sudoers.tmp" ]] || fail "editor not run on /etc/sudoers.tmp: $(cat "$WORK/edlog")"

  "$VISUDO" -c >/dev/null 2>&1 || fail "visudo -c fails after the edit"
  end
}

begin edit-invalid-line-then-exit && {
  XENV=(EDITOR="$ED/append" LINE='foo bar baz')
  answer $'x\n'
  vrun
  expect_rc 0
  expect_out_has 'What now?'
  expect_err_match "^/etc/sudoers:$SYNTAX_LINE:[0-9]+: syntax error"
  expect_unchanged
  expect_no_tmp
  end
}

begin edit-invalid-line-eof-means-exit && {
  XENV=(EDITOR="$ED/append" LINE='foo bar baz')
  vrun
  expect_rc 0
  expect_out_has 'What now?'
  expect_unchanged
  expect_no_tmp
  end
}

begin edit-invalid-line-reedit-then-exit && {
  XENV=(EDITOR="$ED/append" LINE='foo bar baz')
  answer $'e\nx\n'
  vrun
  expect_rc 0
  [[ $(wc -l <"$WORK/edlog") == 2 ]] || fail "editor ran $(wc -l <"$WORK/edlog") times, expected 2"
  expect_unchanged
  expect_no_tmp
  end
}

begin edit-invalid-line-unknown-answer-shows-options && {
  XENV=(EDITOR="$ED/append" LINE='foo bar baz')
  answer $'?\nx\n'
  vrun
  expect_rc 0
  expect_out_has '(e)dit sudoers file again'
  expect_out_has 'e(x)it without saving changes to sudoers file'
  expect_out_has '(Q)uit and save changes to sudoers file (DANGER!)'
  expect_unchanged
  end
}

begin edit-invalid-line-then-Q-installs && {
  XENV=(EDITOR="$ED/append" LINE='foo bar baz')
  answer $'Q\n'
  vrun
  expect_rc 0
  expect_last_line /etc/sudoers 'foo bar baz'
  expect_stat /etc/sudoers '440 root root'
  expect_no_tmp
  end
}

begin edit-semantic-error-then-exit && {
  XENV=(EDITOR="$ED/append" LINE='Defaults foobar')
  answer $'x\n'
  vrun
  expect_rc 0
  expect_err_has 'unknown defaults entry "foobar"'
  expect_unchanged
  expect_no_tmp
  end
}

begin edit-unchanged && {
  XENV=(EDITOR="$ED/noop")
  vrun
  expect_rc 0
  expect_err_has '/etc/sudoers.tmp unchanged'
  expect_unchanged
  expect_no_tmp
  end
}

begin edit-zero-length && {
  XENV=(EDITOR="$ED/empty")
  vrun
  expect_rc 0
  expect_err_has 'zero length temporary file (/etc/sudoers.tmp), /etc/sudoers unchanged'
  expect_unchanged
  expect_no_tmp
  end
}

begin edit-editor-arguments && {

  XENV=(EDITOR="$ED/noop -a -b")
  vrun
  expect_rc 0
  [[ $(cat "$WORK/edlog") == '-a -b -- /etc/sudoers.tmp' ]] || fail "editor args: $(cat "$WORK/edlog")"
  end
}

begin edit-sudo-editor-preferred && {
  XENV=(SUDO_EDITOR="$ED/append" VISUAL="$ED/empty" EDITOR="$ED/empty" LINE='bob ALL=/usr/bin/id')
  vrun
  expect_rc 0
  expect_last_line /etc/sudoers 'bob ALL=/usr/bin/id'
  end
}

begin edit-specified-editor-missing && {
  XENV=(EDITOR=/nonexistent-editor)
  vrun
  expect_rc 1
  expect_err_has 'specified editor (/nonexistent-editor) doesn'"'"'t exist'
  expect_unchanged
  expect_no_tmp
  end
}

begin edit-no-env-editor-uses-editor-list && {

  printf 'Defaults !env_editor\nDefaults editor=%s\n' "$ED/append" >>/etc/sudoers
  XENV=(EDITOR="$ED/empty" LINE='bob ALL=/usr/bin/id')
  vrun
  expect_rc 0
  expect_last_line /etc/sudoers 'bob ALL=/usr/bin/id'
  end
}

begin edit-no-editor-found && {
  printf 'Defaults !env_editor\nDefaults editor=/nonexistent1:/nonexistent2\n' >>/etc/sudoers
  cp -a /etc/sudoers "$WORK/scratch/expected"
  XENV=(EDITOR="$ED/append" LINE='bob ALL=/usr/bin/id')
  vrun
  expect_rc 1
  expect_err_has 'no editor found (editor path = /nonexistent1:/nonexistent2)'
  cmp -s /etc/sudoers "$WORK/scratch/expected" || fail "/etc/sudoers was modified"
  expect_no_tmp
  end
}

begin edit-busy-concurrent && {

  XENV=(EDITOR="$ED/wait" STARTED="$WORK/scratch/started" RELEASE="$WORK/scratch/release")
  env -i PATH=/usr/bin:/bin "${XENV[@]}" timeout 30 "$VISUDO" </dev/null >/dev/null 2>&1 &
  first=$!
  for _ in $(seq 100); do [[ -e $WORK/scratch/started ]] && break; sleep 0.1; done
  [[ -e $WORK/scratch/started ]] || fail "first visudo's editor did not start"
  XENV=(EDITOR="$ED/noop")
  vrun
  touch "$WORK/scratch/release"
  wait "$first"
  expect_rc 1
  expect_err_has '/etc/sudoers busy, try again later'
  [[ $(cat "$WORK/edlog") == "" ]] || fail "second visudo ran its editor"
  expect_unchanged
  expect_no_tmp
  end
}

begin edit-busy-against-sudo-ws && {

  XENV=(EDITOR="$ED/wait" STARTED="$WORK/scratch/started" RELEASE="$WORK/scratch/release")
  env -i PATH=/usr/bin:/bin "${XENV[@]}" timeout 30 "$REFERENCE" </dev/null >/dev/null 2>&1 &
  first=$!
  for _ in $(seq 100); do [[ -e $WORK/scratch/started ]] && break; sleep 0.1; done
  [[ -e $WORK/scratch/started ]] || fail "sudo.ws visudo's editor did not start"
  XENV=(EDITOR="$ED/noop")
  vrun
  touch "$WORK/scratch/release"
  wait "$first"
  expect_rc 1
  expect_err_has '/etc/sudoers busy, try again later'
  expect_unchanged
  end
}

begin edit-sudo-ws-busy-against-selected && {


  XENV=(EDITOR="$ED/wait" STARTED="$WORK/scratch/started" RELEASE="$WORK/scratch/release")
  env -i PATH=/usr/bin:/bin "${XENV[@]}" timeout 30 "$VISUDO" </dev/null >/dev/null 2>&1 &
  first=$!
  for _ in $(seq 100); do [[ -e $WORK/scratch/started ]] && break; sleep 0.1; done
  [[ -e $WORK/scratch/started ]] || fail "lean-sudo visudo's editor did not start"
  XENV=(EDITOR="$ED/noop")
  env -i PATH=/usr/bin:/bin EDLOG="$WORK/edlog" "${XENV[@]}" timeout 30 "$REFERENCE" \
    </dev/null >"$WORK/out" 2>"$WORK/err"
  RC=$? OUT=$(cat "$WORK/out") ERR=$(cat "$WORK/err") CMD="visudo.ws (second)"
  touch "$WORK/scratch/release"
  wait "$first"
  expect_rc 1
  expect_err_has '/etc/sudoers busy, try again later'
  [[ $(cat "$WORK/edlog") == "" ]] || fail "sudo.ws visudo ran its editor"
  expect_unchanged
  expect_no_tmp
  end
}

begin edit-reuses-stale-temp-file && {
  echo 'stale' >/etc/sudoers.tmp
  XENV=(EDITOR="$ED/append" LINE='bob ALL=/usr/bin/id')
  vrun
  expect_rc 0
  expect_last_line /etc/sudoers 'bob ALL=/usr/bin/id'
  ! grep -qx stale /etc/sudoers || fail "stale contents installed"
  expect_no_tmp
  [[ $(wc -l <"$WORK/edlog") == 1 ]] || fail "editor did not run once"
  end
}

begin edit-new-file && {
  XENV=(EDITOR="$ED/append" LINE='bob ALL=/usr/bin/id')
  vrun -f "$WORK/scratch/new"
  expect_rc 0
  expect_last_line "$WORK/scratch/new" 'bob ALL=/usr/bin/id'
  expect_stat "$WORK/scratch/new" '640 root root'
  expect_no_tmp "$WORK/scratch/new.tmp"
  end
}

begin edit-new-file-unchanged-creates-nothing && {
  XENV=(EDITOR="$ED/noop")
  vrun -f "$WORK/scratch/new"
  expect_rc 0
  [[ ! -e $WORK/scratch/new ]] || fail "file created"
  expect_no_tmp "$WORK/scratch/new.tmp"
  end
}

begin edit-file-option-keeps-owner-and-mode && {
  printf 'root ALL=(ALL) ALL\n' >"$WORK/scratch/s"
  chown bob:bob "$WORK/scratch/s"; chmod 0600 "$WORK/scratch/s"
  XENV=(EDITOR="$ED/append" LINE='bob ALL=/usr/bin/id')
  vrun -f "$WORK/scratch/s"
  expect_rc 0
  expect_last_line "$WORK/scratch/s" 'bob ALL=/usr/bin/id'
  expect_stat "$WORK/scratch/s" '600 bob bob'
  end
}

begin edit-file-option-with-O-sets-owner && {
  printf 'root ALL=(ALL) ALL\n' >"$WORK/scratch/s"
  chown bob:bob "$WORK/scratch/s"; chmod 0600 "$WORK/scratch/s"
  XENV=(EDITOR="$ED/append" LINE='bob ALL=/usr/bin/id')
  vrun -O -f "$WORK/scratch/s"
  expect_rc 0
  expect_stat "$WORK/scratch/s" '600 root root'
  end
}

begin edit-as-non-root-refused && {
  XENV=(EDITOR="$ED/append" LINE='bob ALL=(ALL) ALL')
  vrun -u bob
  expect_rc 1
  expect_unchanged
  expect_no_tmp
  end
}





begin help-exit-0 && {
  vrun -h
  expect_rc 0
  expect_out_has 'usage: visudo'
  expect_out_has '-c, --check'
  end
}

begin version-exit-0 && {
  vrun -V
  expect_rc 0
  expect_out_has 'version'
  end
}

begin invalid-option && {
  vrun -z
  expect_rc 1
  expect_err_has "invalid option -- 'z'"
  expect_err_has 'usage: visudo'
  end
}

begin too-many-operands && {
  vrun a b
  expect_rc 1
  expect_err_has 'usage: visudo'
  end
}

begin missing-option-argument && {
  vrun -c -f
  expect_rc 1
  expect_err_has "option requires an argument -- 'f'"
  end
}


compare_reference() {
  local ours_rc=$RC
  sed 's/visudo\.ws/visudo/g' "$WORK/out" >"$WORK/ours.out"
  sed 's/visudo\.ws/visudo/g' "$WORK/err" >"$WORK/ours.err"
  env -i HOME=/root PATH=/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin \
    LANG=C.UTF-8 "${XENV[@]}" "$REFERENCE" "$@" \
    <"$STDIN" >"$WORK/ref.out" 2>"$WORK/ref.err"
  local ref_rc=$?
  [[ $ours_rc == "$ref_rc" ]] || fail "reference rc=$ref_rc, ours rc=$ours_rc"
  sed 's/visudo\.ws/visudo/g' "$WORK/ref.out" >"$WORK/ref.norm.out"
  sed 's/visudo\.ws/visudo/g' "$WORK/ref.err" >"$WORK/ref.norm.err"
  cmp -s "$WORK/ours.out" "$WORK/ref.norm.out" || fail "stdout differs from reference"
  cmp -s "$WORK/ours.err" "$WORK/ref.norm.err" || fail "stderr differs from reference"
}

for flag in '' -s -q -sq; do
  for kind in undefined cycle unused; do
    begin "check-alias-${kind}-${flag:-normal}" && {
      case $kind in
        undefined) printf 'bob FOO = /usr/bin/id\n' >"$WORK/scratch/s";;
        cycle) printf 'User_Alias A = B\nUser_Alias B = A\nA ALL = ALL\n' >"$WORK/scratch/s";;
        unused) printf 'Cmnd_Alias C = /bin/ls\nroot ALL = ALL\n' >"$WORK/scratch/s";;
      esac
      vrun -cf "$WORK/scratch/s" ${flag:+"$flag"}


      if [[ $IS_REF == 0 && $kind != unused ]]; then
        expect_rc 1
        compare_reference -csf "$WORK/scratch/s" ${flag:+"$flag"}
      else
        compare_reference -cf "$WORK/scratch/s" ${flag:+"$flag"}
      fi
      end
    }
  done
done

for directive in @include '#include'; do
  begin "edit-explicit-${directive#\#}-files-in-order" && {
    printf '%s %s\n' "$directive" "$WORK/scratch/child" >"$WORK/scratch/s"
    printf 'root ALL=ALL\n' >"$WORK/scratch/child"
    XENV=(EDITOR="$ED/append" LINE='# changed')
    vrun -f "$WORK/scratch/s"
    expect_rc 0
    expect_out_exactly "press return to edit $WORK/scratch/child: "
    [[ $(cat "$WORK/edlog") == "-- $WORK/scratch/s.tmp"$'\n'"-- $WORK/scratch/child.tmp" ]] ||
      fail "include editor order differs"
    expect_last_line "$WORK/scratch/s" '# changed'
    expect_last_line "$WORK/scratch/child" '# changed'
    expect_no_tmp "$WORK/scratch/child.tmp"
    end
  }
done

begin edit-no-includes-still-checks-include && {
  printf '@include %s\n' "$WORK/scratch/child" >"$WORK/scratch/s"
  printf 'foo bar baz\n' >"$WORK/scratch/child"
  XENV=(EDITOR="$ED/append" LINE='# changed')
  answer $'x\n'
  vrun -I -f "$WORK/scratch/s"
  expect_rc 0
  expect_out_exactly 'What now? '
  [[ $(wc -l <"$WORK/edlog") == 1 ]] || fail "-I edited include"
  expect_err_has "$WORK/scratch/child:1:"
  [[ $(wc -l <"$WORK/scratch/s") == 1 ]] || fail "discard installed main file"
  expect_no_tmp "$WORK/scratch/s.tmp"
  end
}

begin edit-includes-discard-entire-session && {
  printf '@include %s\n' "$WORK/scratch/child" >"$WORK/scratch/s"
  printf 'root ALL=ALL\n' >"$WORK/scratch/child"
  cp "$WORK/scratch/s" "$WORK/scratch/orig-main"
  cp "$WORK/scratch/child" "$WORK/scratch/orig-child"
  XENV=(EDITOR="$ED/append" LINE='foo bar baz')
  answer $'\nx\n'
  vrun -f "$WORK/scratch/s"
  expect_rc 0
  cmp -s "$WORK/scratch/s" "$WORK/scratch/orig-main" || fail "main partially installed"
  cmp -s "$WORK/scratch/child" "$WORK/scratch/orig-child" || fail "child partially installed"
  expect_no_tmp "$WORK/scratch/s.tmp"
  expect_no_tmp "$WORK/scratch/child.tmp"
  end
}

for noincludes in '' -I; do
begin "edit-new-include-added-during-session-${noincludes:-normal}" && {
  printf 'root ALL=ALL\n' >"$WORK/scratch/s"
  printf 'root ALL=ALL\n' >"$WORK/scratch/child"
  cat >"$ED/add-include" <<'EOF'
#!/bin/sh
for a; do f=$a; done
printf '%s\n' "$*" >>"$EDLOG"
case "$f" in
  */s.tmp) printf '@include %s\n' "$CHILD" >>"$f";;
  *) printf '# child changed\n' >>"$f";;
esac
EOF
  chmod 0755 "$ED/add-include"
  XENV=(EDITOR="$ED/add-include" CHILD="$WORK/scratch/child")
  vrun ${noincludes:+"$noincludes"} -f "$WORK/scratch/s"
  expect_rc 0
  expect_out_exactly "press return to edit $WORK/scratch/child: "
  expect_last_line "$WORK/scratch/child" '# child changed'
  [[ $(wc -l <"$WORK/edlog") == 2 ]] || fail "new include not edited once"
  expect_no_tmp "$WORK/scratch/child.tmp"
  end
}
done

begin edit-includedir-not-edited && {
  mkdir "$WORK/scratch/d"
  printf '@includedir %s\n' "$WORK/scratch/d" >"$WORK/scratch/s"
  printf 'root ALL=ALL\n' >"$WORK/scratch/d/child"
  XENV=(EDITOR="$ED/append" LINE='# changed')
  vrun -f "$WORK/scratch/s"
  expect_rc 0
  expect_out_empty
  [[ $(wc -l <"$WORK/edlog") == 1 ]] || fail "includedir entry edited"
  expect_last_line "$WORK/scratch/d/child" 'root ALL=ALL'
  end
}

begin edit-quiet-unchanged-still-reported && {
  XENV=(EDITOR="$ED/noop")
  vrun -q
  expect_rc 0
  expect_err_has '/etc/sudoers.tmp unchanged'
  expect_no_tmp
  end
}

begin edit-unchanged-enforces-owner-mode && {
  printf 'root ALL=ALL\n' >"$WORK/scratch/s"
  chown bob:bob "$WORK/scratch/s"
  chmod 0600 "$WORK/scratch/s"
  XENV=(EDITOR="$ED/noop")
  vrun -OPf "$WORK/scratch/s"
  expect_rc 0
  expect_stat "$WORK/scratch/s" '440 root root'
  end
}

begin check-no-includes-still-loads-files && {
  printf '@include %s\n' "$WORK/scratch/child" >"$WORK/scratch/s"
  printf 'root ALL=ALL\n' >"$WORK/scratch/child"
  vrun -cIf "$WORK/scratch/s"
  compare_reference -cIf "$WORK/scratch/s"
  end
}

for opt in -x --export; do
  begin "export-${opt#--}-ubuntu-command-lookup" && {
    printf 'root ALL=ALL\n' >"$WORK/scratch/s"
    vrun -q -f "$WORK/scratch/s" "$opt" "$WORK/scratch/json"
    compare_reference -q -f "$WORK/scratch/s" "$opt" "$WORK/scratch/json"
    end
  }
  begin "export-${opt#--}-json-via-cvtsudoers" && {
    mkdir "$WORK/scratch/bin"
    ln -s /usr/bin/cvtsudoers.ws "$WORK/scratch/bin/cvtsudoers"
    printf 'User_Alias OPS = bob, root\nOPS ALL=(ALL:ALL) NOPASSWD: /usr/bin/id\n' >"$WORK/scratch/s"
    XENV=(PATH="$WORK/scratch/bin:/usr/bin:/bin")
    vrun -f "$WORK/scratch/s" "$opt" "$WORK/scratch/json"
    expect_rc 0
    cp "$WORK/scratch/json" "$WORK/scratch/ours.json"
    compare_reference -f "$WORK/scratch/s" "$opt" "$WORK/scratch/json"
    cmp -s "$WORK/scratch/ours.json" "$WORK/scratch/json" || fail "JSON differs from reference"
    end
  }
done

for opt in -h -V -hz -Vh --help --version; do
  begin "cli-exact-$opt" && {
    vrun "$opt"
    compare_reference "$opt"
    end
  }
done

for kind in unknown-default invalid-default duplicate unused-undefined unused-cycle mixed missing-include syntax; do
  for flag in '' -s -q; do
    begin "check-exact-${kind}-${flag:-normal}" && {
      case $kind in
        unknown-default) text='Defaults foobar\n';;
        invalid-default) text='Defaults passwd_tries=abc\n';;
        duplicate) text='User_Alias A = bob\nUser_Alias A = carol\nA ALL=ALL\n';;
        unused-undefined) text='User_Alias A = MISSING\nroot ALL=ALL\n';;
        unused-cycle) text='User_Alias A = B\nUser_Alias B = A\nroot ALL=ALL\n';;
        mixed) text='Defaults foobar\nCmnd_Alias UNUSED = /bin/ls\nbob FOO=/bin/ls\n';;
        missing-include) text='@include /nonexistent-file\n';;
        syntax) text='foo bar baz\n';;
      esac
      printf '%b' "$text" >"$WORK/scratch/s"
      vrun -cf "$WORK/scratch/s" ${flag:+"$flag"}


      if [[ $IS_REF == 0 && $kind == unused-* ]]; then
        expect_rc 1
        expect_out_empty
        if [[ $flag == -q ]]; then
          expect_err_empty
        elif [[ $kind == unused-undefined ]]; then
          expect_err_has 'User_Alias "MISSING" referenced but not defined'
        else
          expect_err_has 'cycle in User_Alias'
        fi
      else
        compare_reference -cf "$WORK/scratch/s" ${flag:+"$flag"}
      fi
      end
    }
  done
done

begin check-stdin-owner-perms && {
  printf 'root ALL=ALL\n' >"$WORK/scratch/input"
  STDIN="$WORK/scratch/input"
  vrun -cOPf -
  compare_reference -cOPf -
  end
}

begin edit-empty-include-installed && {
  printf '@include %s\n' "$WORK/scratch/child" >"$WORK/scratch/s"
  printf 'root ALL=ALL\n' >"$WORK/scratch/child"
  cat >"$ED/empty-child" <<'EOF'
#!/bin/sh
for a; do f=$a; done
case "$f" in */child.tmp) : >"$f";; esac
EOF
  chmod 0755 "$ED/empty-child"
  XENV=(EDITOR="$ED/empty-child")
  vrun -f "$WORK/scratch/s"
  expect_rc 0
  [[ -f $WORK/scratch/child && ! -s $WORK/scratch/child ]] || fail "empty include not installed"
  expect_no_tmp "$WORK/scratch/child.tmp"
  end
}

begin edit-reedit-include-under-no-includes && {
  printf '@include %s\n' "$WORK/scratch/child" >"$WORK/scratch/s"
  printf 'foo bar baz\n' >"$WORK/scratch/child"
  cat >"$ED/fix-child" <<'EOF'
#!/bin/sh
for a; do f=$a; done
printf '%s\n' "$*" >>"$EDLOG"
case "$f" in */child.tmp) printf 'root ALL=ALL\n' >"$f";; esac
EOF
  chmod 0755 "$ED/fix-child"
  XENV=(EDITOR="$ED/fix-child")
  answer $'e\n'
  vrun -If "$WORK/scratch/s"
  expect_rc 0
  expect_last_line "$WORK/scratch/child" 'root ALL=ALL'
  [[ $(wc -l <"$WORK/edlog") == 2 ]] || fail "include error not re-edited"
  expect_no_tmp "$WORK/scratch/child.tmp"
  end
}

begin edit-busy-explicit-include && {
  printf '@include %s\n' "$WORK/scratch/child" >"$WORK/scratch/s"
  printf 'root ALL=ALL\n' >"$WORK/scratch/child"
  XENV=(EDITOR="$ED/wait" STARTED="$WORK/scratch/started" RELEASE="$WORK/scratch/release")
  env -i PATH=/usr/bin:/bin "${XENV[@]}" timeout 30 "$VISUDO" -f "$WORK/scratch/s" \
    </dev/null >/dev/null 2>&1 &
  first=$!
  for _ in $(seq 100); do [[ -e $WORK/scratch/started ]] && break; sleep 0.1; done
  [[ -e $WORK/scratch/started ]] || fail "first editor did not start"
  XENV=(EDITOR="$ED/noop")
  vrun -f "$WORK/scratch/child"
  touch "$WORK/scratch/release"
  wait "$first"
  expect_rc 1
  expect_err_has "$WORK/scratch/child busy, try again later"
  expect_no_tmp "$WORK/scratch/s.tmp"
  expect_no_tmp "$WORK/scratch/child.tmp"
  end
}

begin edit-signal-cleans-temporary-copy && {
  XENV=(EDITOR="$ED/wait" STARTED="$WORK/scratch/started" RELEASE="$WORK/scratch/release")
  env -i PATH=/usr/bin:/bin "${XENV[@]}" "$VISUDO" \
    </dev/null >"$WORK/out" 2>"$WORK/err" &
  first=$!
  for _ in $(seq 100); do [[ -e $WORK/scratch/started ]] && break; sleep 0.1; done
  [[ -e $WORK/scratch/started ]] || fail "editor did not start"
  kill -TERM "$first"
  wait "$first"
  RC=$? OUT=$(cat "$WORK/out") ERR=$(cat "$WORK/err") CMD="visudo (SIGTERM)"
  touch "$WORK/scratch/release"
  expect_rc 15
  expect_err_has 'exiting due to signal: Terminated'
  expect_unchanged
  expect_no_tmp
  end
}

for status in exit signal; do
  begin "edit-editor-$status-status" && {
    cat >"$ED/status" <<'EOF'
#!/bin/sh
for a; do f=$a; done
printf '# changed\n' >>"$f"
if [ "$STATUS" = signal ]; then kill -TERM $$; else exit 7; fi
EOF
    chmod 0755 "$ED/status"
    XENV=(EDITOR="$ED/status" STATUS="$status")
    vrun
    expect_rc 0
    if [[ $status == signal ]]; then
      expect_unchanged
      expect_err_has "editor ($ED/status) failed, /etc/sudoers unchanged"
    else
      expect_last_line /etc/sudoers '# changed'
      expect_err_empty
    fi
    expect_no_tmp
    end
  }
done

begin edit-dash-is-literal-filename && {
  XENV=(EDITOR="$ED/append" LINE='root ALL=ALL')
  pushd "$WORK/scratch" >/dev/null
  vrun -f -
  popd >/dev/null
  expect_rc 0
  expect_last_line "$WORK/scratch/-" 'root ALL=ALL'
  expect_stat "$WORK/scratch/-" '640 root root'
  expect_no_tmp "$WORK/scratch/-.tmp"
  end
}

begin edit-refused-undefined-alias-keeps-sudo-working && {


  chown root:root "$SUDO"
  chmod 4755 "$SUDO"
  "$SUDO" -n /usr/bin/true || fail "sudo failed before editing"
  XENV=(EDITOR="$ED/append" LINE='bob UNDEFINED_HOST = /usr/bin/id')
  answer $'x\n'
  if [[ $IS_REF == 1 ]]; then vrun -s; else vrun; fi
  expect_rc 0
  expect_out_has 'What now?'
  expect_err_has 'Host_Alias "UNDEFINED_HOST" referenced but not defined'
  expect_unchanged
  expect_no_tmp
  "$SUDO" -n /usr/bin/true || fail "sudo failed after rejected edit"
  end
}

begin edit-unchanged-symlink-include-keeps-later-edits && {
  printf 'root ALL=ALL\n' >"$WORK/scratch/target"
  chown bob:bob "$WORK/scratch/target"
  chmod 0600 "$WORK/scratch/target"
  ln -s "$WORK/scratch/target" "$WORK/scratch/a"
  printf 'root ALL=ALL\n' >"$WORK/scratch/b"
  chmod 0440 "$WORK/scratch/b"
  printf '@include %s\n@include %s\n' "$WORK/scratch/a" "$WORK/scratch/b" >>/etc/sudoers
  cat >"$ED/symlink-session" <<'EOF'
#!/bin/sh
for a; do f=$a; done
case "$f" in
  */a.tmp) ;;
  *) printf '# edited\n' >>"$f";;
esac
EOF
  chmod 0755 "$ED/symlink-session"
  XENV=(EDITOR="$ED/symlink-session")
  vrun
  expect_rc 0
  expect_last_line /etc/sudoers '# edited'
  expect_last_line "$WORK/scratch/b" '# edited'
  [[ -L $WORK/scratch/a ]] || fail "unchanged include symlink replaced"
  expect_stat "$WORK/scratch/target" '440 root root'
  expect_no_tmp
  expect_no_tmp "$WORK/scratch/a.tmp"
  expect_no_tmp "$WORK/scratch/b.tmp"
  "$VISUDO" -c >/dev/null 2>&1 || fail "installed policy does not validate"
  end
}

begin edit-install-error-continues-with-later-files && {
  printf 'root ALL=ALL\n' >"$WORK/scratch/a"
  printf 'root ALL=ALL\n' >"$WORK/scratch/b"
  chmod 0440 "$WORK/scratch/a" "$WORK/scratch/b"
  printf '@include %s\n@include %s\n' "$WORK/scratch/a" "$WORK/scratch/b" >>/etc/sudoers
  cat >"$ED/install-error" <<'EOF'
#!/bin/sh
for a; do f=$a; done
printf '# edited\n' >>"$f"
case "$f" in
  */b.tmp) rm "$FAIL_TARGET"; mkdir "$FAIL_TARGET";;
esac
EOF
  chmod 0755 "$ED/install-error"
  XENV=(EDITOR="$ED/install-error" FAIL_TARGET="$WORK/scratch/a")
  vrun
  expect_rc 1
  expect_last_line /etc/sudoers '# edited'
  expect_last_line "$WORK/scratch/b" '# edited'
  expect_last_line "$WORK/scratch/a.tmp" '# edited'
  expect_err_has "contents of edit session left in $WORK/scratch/a.tmp"
  expect_no_tmp
  expect_no_tmp "$WORK/scratch/b.tmp"
  end
}



for scope in global unset user other-user host other-host runas command sudo-user parser-order; do
  for mode in check quiet-check edit quiet-edit; do
    begin "defaults-callback-$scope-$mode" && {
      case $scope in
        global) line='Defaults runchroot="/"';;
        unset) line='Defaults !runchroot';;
        user) line='Defaults:root runchroot="/"';;
        other-user) line='Defaults:nobody runchroot="/"';;
        host) line='Defaults@sudo-it runchroot="/"';;
        other-host) line='Defaults@other-host runchroot="/"';;
        runas) line='Defaults>root runchroot="/"';;
        command) line='Defaults!/usr/bin/true runchroot="/"';;
        sudo-user) line='Defaults:bob runchroot="/"';;
        parser-order) line='Defaults runchroot="/"';;
      esac
      printf '%s\nroot ALL=ALL\n' "$line" >"$WORK/scratch/s"
      if [[ $scope == parser-order ]]; then
        printf 'root ALL=CHROOT=/ /usr/bin/true\n' >>"$WORK/scratch/s"
      fi
      XENV=(EDITOR="$ED/noop")
      [[ $scope != sudo-user ]] || XENV+=(SUDO_USER=bob)
      options=(-f "$WORK/scratch/s")
      case $mode in
        check) options+=(-c);;
        quiet-check) options+=(-cq);;
        quiet-edit) options+=(-q);;
      esac
      vrun "${options[@]}"
      expect_rc 0
      compare_reference "${options[@]}"
      expect_no_tmp "$WORK/scratch/s.tmp"
      end
    }
  done
done





emit "1..$NUM"
emit "# implementation: $LABEL ($VISUDO)"
emit "# passed: $PASSED/$NUM (skipped: $SKIPPED), failed: $FAILED"
for n in "${FAILED_NAMES[@]}"; do emit "# FAILED: $n"; done
reset_state
rm -rf "$WORK"
[[ $NUM -gt 0 ]] || { echo "# no tests matched filter '$FILTER'"; exit 2; }
[[ $FAILED -eq 0 ]]
