#!/bin/bash
# End-to-end visudo tests. Runs INSIDE the test container as root (see
# `run.sh --visudo`); same image, conventions and TAP output as tests.sh.
#
#   visudo-tests.sh VISUDO_BINARY [NAME_FILTER]
#
# VISUDO_BINARY is run directly as root (reference: /usr/sbin/visudo.ws).
# Expectations are the ACTUAL behaviour of sudo.ws 1.9.17p2's visudo; where
# lean-sudo deliberately differs the test says so and is skipped for the
# reference.
set -u

VISUDO=${1:?usage: visudo-tests.sh VISUDO_BINARY [NAME_FILTER]}
FILTER=${2:-}
LABEL=${IMPL_LABEL:-$(basename "$VISUDO")}
OUTDIR=${OUTDIR:-/out}
WORK=$(mktemp -d /tmp/visudo-it.XXXXXX)
chmod 0755 "$WORK"
REFERENCE=/usr/sbin/visudo.ws
CMD_TIMEOUT=40
[[ $VISUDO == "$REFERENCE" ]] && IS_REF=1 || IS_REF=0

[[ -f $VISUDO ]] || { echo "Bail out! $VISUDO does not exist"; exit 2; }
chmod 0755 "$VISUDO"

cp -a /etc/sudoers "$WORK/sudoers.orig"
cp -a /etc/sudoers.d "$WORK/sudoers.d.orig"

# --- editor scripts (the temp file is the last argument) --------------------
ED=$WORK/ed
mkdir -p "$ED"
cat >"$ED/append" <<'EOF'
#!/bin/sh
# appends $LINE; records its arguments and how often it ran
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
# signals that it runs, then waits (max ~20 s) for the release file
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

# ---------------------------------------------------------------------------
# Harness (as in tests.sh)
# ---------------------------------------------------------------------------

NUM=0 PASSED=0 FAILED=0 SKIPPED=0
FAILED_NAMES=()
CUR= CMD= RC= OUT= ERR=
FAILS=()
XENV=()   # extra environment for the next `vrun`
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

# skip REASON: report the current test as skipped (returns 1 to end the block)
skip() {
  NUM=$((NUM + 1)) SKIPPED=$((SKIPPED + 1))
  emit "ok $NUM - $CUR # SKIP $1"
  return 1
}

# vrun [-u USER] ARGS...: run "$VISUDO ARGS..." as root (or USER) with a clean
# environment plus XENV, stdin from $STDIN. Sets RC, OUT, ERR.
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

# answer TEXT: stdin for the next vrun (the What now? answers)
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
# expect_stat PATH 'MODE OWNER GROUP' (stat -c '%a %U %G')
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

STOCK_OK="/etc/sudoers: parsed OK
/etc/sudoers.d/README: parsed OK
/etc/sudoers.d/carol: parsed OK
/etc/sudoers.d/dave: parsed OK
/etc/sudoers.d/erin: parsed OK
/etc/sudoers.d/frank: parsed OK"
SYNTAX_LINE=$(($(wc -l </etc/sudoers) + 1))

# ===========================================================================
# Check mode
# ===========================================================================

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
  expect_err_has 'foo bar baz'   # the offending line is echoed
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
  # -f disables the owner/mode checks unless -O/-P are given
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
  # sudo.ws only warns (an error with -s); lean-sudo's sudo refuses such a
  # policy, so its visudo must reject it. Same expectation under -s.
  printf 'bob FOO = /usr/bin/id\n' >"$WORK/scratch/s"
  vrun -c -s -f "$WORK/scratch/s"
  expect_rc 1
  expect_err_has 'Host_Alias "FOO" referenced but not defined'
  end
}

# ===========================================================================
# Edit mode
# ===========================================================================

begin edit-append-valid-line && {
  chmod 0640 /etc/sudoers   # installation must restore 0440 root:root
  XENV=(EDITOR="$ED/append" LINE='bob ALL=(ALL) /usr/bin/id')
  vrun
  expect_rc 0
  expect_last_line /etc/sudoers 'bob ALL=(ALL) /usr/bin/id'
  expect_stat /etc/sudoers '440 root root'
  expect_no_tmp
  [[ $(head -n 1 "$WORK/edlog") == *"/etc/sudoers.tmp" ]] || fail "editor not run on /etc/sudoers.tmp: $(cat "$WORK/edlog")"
  # the result is accepted by a full check
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
  # words of $EDITOR are kept; sudo.ws passes "--" before the file
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
  # !env_editor: $EDITOR is ignored unless it is in the editor list
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
  # a second visudo while the first one's editor is running
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
  # a sudo.ws visudo holds the lock: lean-sudo's visudo must back off
  if [[ $IS_REF == 1 ]]; then skip "lean-sudo interoperability check"; else
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
  end; fi
}

begin edit-sudo-ws-busy-against-lean && {
  # the reverse: sudo.ws's visudo ignores the temp file, so this checks that
  # lean-sudo's lock (F_OFD_SETLK) conflicts with sudo.ws's fcntl lock
  if [[ $IS_REF == 1 ]]; then skip "lean-sudo interoperability check"; else
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
  end; fi
}

begin edit-busy-stale-temp-file && {
  # lean-sudo creates <file>.tmp with O_EXCL; an existing one means busy.
  # (sudo.ws's visudo truncates and reuses it instead.)
  if [[ $IS_REF == 1 ]]; then skip "sudo.ws reuses an existing temp file"; else
  echo 'stale' >/etc/sudoers.tmp
  XENV=(EDITOR="$ED/append" LINE='bob ALL=/usr/bin/id')
  vrun
  expect_rc 1
  expect_err_has '/etc/sudoers busy, try again later'
  expect_unchanged
  [[ $(cat /etc/sudoers.tmp) == stale ]] || fail "stale temp file was modified"
  [[ $(cat "$WORK/edlog") == "" ]] || fail "editor ran"
  end; fi
}

begin edit-new-file && {
  XENV=(EDITOR="$ED/append" LINE='bob ALL=/usr/bin/id')
  vrun -f "$WORK/scratch/new"
  expect_rc 0
  expect_last_line "$WORK/scratch/new" 'bob ALL=/usr/bin/id'
  # sudo.ws creates a new -f file 0640, lean-sudo 0440; both root:root.
  [[ $(stat -c '%a %U %G' "$WORK/scratch/new") =~ ^[46]40\ root\ root$ ]] ||
    fail "new file: expected 440/640 root root, got $(stat -c '%a %U %G' "$WORK/scratch/new")"
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

# ===========================================================================
# Command line
# ===========================================================================

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

# ---------------------------------------------------------------------------
# Summary
# ---------------------------------------------------------------------------

emit "1..$NUM"
emit "# implementation: $LABEL ($VISUDO)"
emit "# passed: $PASSED/$NUM (skipped: $SKIPPED), failed: $FAILED"
for n in "${FAILED_NAMES[@]}"; do emit "# FAILED: $n"; done
reset_state
rm -rf "$WORK"
[[ $NUM -gt 0 ]] || { echo "# no tests matched filter '$FILTER'"; exit 2; }
[[ $FAILED -eq 0 ]]
