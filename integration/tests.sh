#!/bin/bash











set -u

IMPL_BIN=${1:?usage: tests.sh SUDO_BINARY [NAME_FILTER]}
FILTER=${2:-}
LABEL=${IMPL_LABEL:-$(basename "$IMPL_BIN")}
OUTDIR=${OUTDIR:-/out}
WORK=$(mktemp -d /tmp/sudo-it.XXXXXX)
chmod 0755 "$WORK"
USER_PATH=/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin
SECURE_PATH=/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin:/snap/bin
PTYRUN=/opt/sudo-it/ptyrun.py
CMD_TIMEOUT=40





[[ -f $IMPL_BIN ]] || { echo "Bail out! $IMPL_BIN does not exist"; exit 2; }
rm -f /usr/bin/sudo /usr/bin/sudoedit
install -o root -g root -m 4755 "$IMPL_BIN" /usr/bin/sudo
ln -s sudo /usr/bin/sudoedit



host=$(hostname)
getent hosts "$host" >/dev/null || echo "127.0.1.1 $host" >>/etc/hosts


cp -a /etc/sudoers "$WORK/sudoers.orig"
cp -a /etc/sudoers.d "$WORK/sudoers.d.orig"

touch /tmp/frankfile

mkdir -p "$OUTDIR"
LOG="$OUTDIR/${IMPL_OUTPUT_LABEL:-$LABEL}.log"
TAP="$OUTDIR/${IMPL_OUTPUT_LABEL:-$LABEL}.tap"
: >"$LOG"
: >"$TAP"

if [[ -n ${HOST_UID:-} ]]; then chown "$HOST_UID:${HOST_GID:-$HOST_UID}" "$LOG" "$TAP"; fi

uid_of() { id -u "$1"; }
gid_of() { id -g "$1"; }

reset_state() {

  rm -rf /run/sudo /var/run/sudo /var/lib/sudo/ts /var/lib/sudo/lectured/* \
         /var/run/sudo-rs /run/sudo-rs /var/db/sudo
  rm -rf /etc/sudoers.d
  cp -a "$WORK/sudoers.d.orig" /etc/sudoers.d
  cp -a "$WORK/sudoers.orig" /etc/sudoers
  chown root:root /etc/sudoers; chmod 0440 /etc/sudoers
}






cat >/usr/local/lib/sudo_it_logging.py <<'PY'
import json
import pathlib
import subprocess
import tempfile
import time
import uuid

class Syslog:
    def __enter__(self):
        self.tmp = tempfile.TemporaryDirectory(prefix='sudo-rsyslog-')
        root = pathlib.Path(self.tmp.name)
        self.output = root / 'messages'
        self.diagnostics = (root / 'stderr').open('w+')
        config = root / 'rsyslog.conf'
        config.write_text(
            'global(maxMessageSize="256k" parser.escapeControlCharactersOnReceive="off")\n'
            'module(load="imuxsock" SysSock.Name="/dev/log" SysSock.RateLimit.Interval="0")\n'
            'template(name="raw" type="list") { constant(value="{") '
            'property(name="rawmsg" format="jsonf") constant(value="}\\n") }\n'
            '*.* action(type="omfile" file="' + str(self.output) +
            '" template="raw" flushOnTXEnd="on")\n')
        self.process = subprocess.Popen(
            ['rsyslogd', '-n', '-i', str(root / 'pid'), '-f', str(config)],
            stdout=self.diagnostics, stderr=self.diagnostics)
        try:
            self.wait(lambda: pathlib.Path('/dev/log').is_socket())
            self.drain()
            self.offset = self.output.stat().st_size
            return self
        except BaseException:
            self.__exit__(None, None, None)
            raise

    def wait(self, predicate):
        deadline = time.monotonic() + 10
        while not predicate():
            if self.process.poll() is not None or time.monotonic() >= deadline:
                self.diagnostics.seek(0)
                raise AssertionError('rsyslog readiness/drain failed: ' + self.diagnostics.read())
            time.sleep(.01)

    def drain(self):
        marker = 'sudo-it-drain-' + uuid.uuid4().hex
        subprocess.run(['logger', '--socket', '/dev/log', '--', marker], check=True)
        self.wait(lambda: self.output.exists() and marker in self.output.read_text())
        return marker

    def messages(self):
        marker = self.drain()
        with self.output.open() as stream:
            stream.seek(self.offset)
            records = [json.loads(line)['rawmsg'] for line in stream]
        return [record for record in records if marker not in record]

    def __exit__(self, *args):
        self.process.terminate()
        self.process.wait(timeout=10)
        self.diagnostics.close()
        self.tmp.cleanup()
PY


NUM=0 PASSED=0 FAILED=0
FAILED_NAMES=()
CUR= CMD= RC= OUT= ERR=
FAILS=()
XENV=()

emit() { printf '%s\n' "$*" | tee -a "$TAP" "$LOG"; }


begin() {
  CUR=$1
  if [[ -n $FILTER ]] && ! [[ $CUR =~ $FILTER ]]; then return 1; fi
  FAILS=() XENV=() CMD= RC= OUT= ERR=
  reset_state
  printf '\n=== %s\n' "$CUR" >>"$LOG"
  return 0
}



run() {
  local user=$1 home
  CMD=$2
  home=$(getent passwd "$user" | cut -d: -f6)
  env -i HOME="$home" USER="$user" LOGNAME="$user" SHELL=/bin/bash \
      PATH="$USER_PATH" LANG=C.UTF-8 "${XENV[@]}" \
    timeout -k 5 "$CMD_TIMEOUT" \
    setpriv --reuid="$user" --regid="$(gid_of "$user")" --init-groups -- \
    /bin/sh -c "cd \"\$HOME\" || exit 99; $CMD" \
    >"$WORK/out" 2>"$WORK/err" </dev/null
  RC=$?
  OUT=$(cat "$WORK/out")
  ERR=$(cat "$WORK/err")
  {
    printf -- '--- run as %s: %s\n' "$user" "$CMD"
    [[ ${#XENV[@]} -gt 0 ]] && printf -- '--- extra env: %s\n' "${XENV[*]}"
    printf -- '--- rc=%s\n--- stdout:\n%s\n--- stderr:\n%s\n' "$RC" "$OUT" "$ERR"
  } >>"$LOG"
}




pty() {
  local user=$1
  CMD=$2
  shift 2
  timeout -k 5 "$CMD_TIMEOUT" "$PTYRUN" "$user" "$CMD" "$@" >"$WORK/out" 2>"$WORK/err" </dev/null
  RC=$?
  OUT=$(cat "$WORK/out")
  ERR=$(cat "$WORK/err")
  {
    printf -- '--- pty as %s: %s  [%s]\n' "$user" "$CMD" "$*"
    printf -- '--- rc=%s\n--- transcript:\n%s\n--- ptyrun:\n%s\n' "$RC" "$OUT" "$ERR"
  } >>"$LOG"
}

fail() { FAILS+=("$1"); }

expect_rc() {
  [[ $RC == "$1" ]] || fail "exit status: expected $1, got $RC"
}
expect_rc_not() {
  [[ $RC != "$1" ]] || fail "exit status: expected anything but $1, got $RC"
}

expect_out_line() {
  grep -qxF -- "$1" <<<"$OUT" || fail "stdout: expected a line equal to '$1'"
}
expect_out_has() {
  grep -qF -- "$1" <<<"$OUT" || fail "stdout: expected to contain '$1'"
}
expect_out_lacks() {
  ! grep -qF -- "$1" <<<"$OUT" || fail "stdout: expected NOT to contain '$1'"
}
expect_out_empty() {
  [[ -z $OUT ]] || fail "stdout: expected empty"
}
expect_err_has() {
  grep -qF -- "$1" <<<"$ERR" || fail "stderr: expected to contain '$1'"
}

expect_err_match() {
  grep -qE -- "$1" <<<"$ERR" || fail "stderr: expected to match /$1/"
}
expect_err_lacks() {
  ! grep -qF -- "$1" <<<"$ERR" || fail "stderr: expected NOT to contain '$1'"
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


NOT_IN_SUDOERS='is not in the sudoers file'
NOT_ALLOWED='is not allowed to execute'
PW_REQUIRED='a password is required'







begin alice-stdin-password && {
  run alice "echo alicepw | sudo -S id -u"
  expect_rc 0
  expect_out_line 0
  expect_err_has '[sudo] password for alice:'
  end
}

begin alice-wrong-password-three-times && {
  run alice "printf 'bad1\nbad2\nbad3\n' | sudo -S id -u"
  expect_rc 1
  expect_out_empty
  expect_err_has 'Sorry, try again.'
  expect_err_has '3 incorrect password attempts'
  end
}

begin alice-wrong-then-right-password && {
  run alice "printf 'bad1\nalicepw\n' | sudo -S id -u"
  expect_rc 0
  expect_out_line 0
  expect_err_has 'Sorry, try again.'
  end
}

begin alice-noninteractive-without-timestamp && {
  run alice "sudo -n id -u"
  expect_rc 1
  expect_out_empty
  expect_err_has "$PW_REQUIRED"
  end
}

begin alice-no-tty-no-stdin-flag && {
  run alice "sudo id -u"
  expect_rc 1
  expect_out_empty
  expect_err_has 'a terminal is required'
  end
}

begin root-needs-no-password && {
  run root "sudo -n id -un"
  expect_rc 0
  expect_out_line root
  end
}



begin bob-not-in-sudoers && {


  run bob "echo bobpw | sudo -S id -u"
  expect_rc 1
  expect_out_empty
  expect_err_has "bob $NOT_IN_SUDOERS"
  end
}

begin bob-noninteractive-denied && {


  run bob "sudo -n id -u"
  expect_rc 1
  expect_out_empty
  expect_err_match "$PW_REQUIRED|$NOT_IN_SUDOERS"
  end
}

begin alice-runas-other-user && {
  run alice "echo alicepw | sudo -S -u bob id -un"
  expect_rc 0
  expect_out_line bob
  end
}

begin alice-runas-group && {
  run alice "echo alicepw | sudo -S -g adm id -gn"
  expect_rc 0
  expect_out_line adm
  end
}

begin alice-runas-uid-hash && {
  run alice "echo alicepw | sudo -S -u '#0' id -u"
  expect_rc 0
  expect_out_line 0
  end
}

begin carol-nopasswd-id && {
  run carol "sudo -n id -u"
  expect_rc 0
  expect_out_line 0
  end
}

begin carol-nopasswd-whoami && {
  run carol "sudo -n whoami"
  expect_rc 0
  expect_out_line root
  end
}

begin carol-double-dash && {
  run carol "sudo -n -- id -u"
  expect_rc 0
  expect_out_line 0
  end
}

begin carol-cat-denied && {
  run carol "echo carolpw | sudo -S cat /etc/hostname"
  expect_rc 1
  expect_out_empty
  expect_err_has "carol $NOT_ALLOWED"
  end
}

begin carol-cat-noninteractive-denied && {


  run carol "sudo -n cat /etc/hostname"
  expect_rc 1
  expect_out_empty
  expect_err_match "$PW_REQUIRED|$NOT_ALLOWED"
  end
}

begin carol-runas-bob-with-password && {
  run carol "echo carolpw | sudo -S -u bob id -un"
  expect_rc 0
  expect_out_line bob
  expect_err_has '[sudo] password for carol:'
  end
}

begin carol-runas-bob-needs-password && {
  run carol "sudo -n -u bob id -un"
  expect_rc 1
  expect_out_empty
  expect_err_has "$PW_REQUIRED"
  end
}

begin carol-runas-alice-denied && {
  run carol "echo carolpw | sudo -S -u alice id"
  expect_rc 1
  expect_out_empty
  expect_err_has "carol $NOT_ALLOWED"
  end
}

begin dave-su-denied && {
  run dave "echo davepw | sudo -S su -c true"
  expect_rc 1
  expect_out_empty
  expect_err_has "dave $NOT_ALLOWED"
  end
}

begin dave-shell-alias-denied && {
  run dave "echo davepw | sudo -S bash -c 'echo pwned'"
  expect_rc 1
  expect_out_empty
  expect_err_has "dave $NOT_ALLOWED"
  end
}

begin dave-id-allowed && {
  run dave "echo davepw | sudo -S id -u"
  expect_rc 0
  expect_out_line 0
  end
}

begin gina-alias-inner-deny && {




  run gina "echo ginapw | sudo -S whoami"
  expect_rc 1
  expect_out_empty
  expect_err_has "gina $NOT_ALLOWED"
  end
}

begin gina-alias-inner-allow && {
  run gina "sudo -n id -u"
  expect_rc 0
  expect_out_line 0
  end
}

begin gina-alias-other-command-allowed-by-all && {
  run gina "sudo -n env true && echo ok"
  expect_rc 0
  expect_out_line ok
  end
}

begin erin-group-only-runas && {
  run erin "sudo -n -g adm id -gn && sudo -n -g adm id -un"
  expect_rc 0
  expect_out_line adm
  expect_out_line erin
  end
}

begin erin-user-and-group-denied && {
  run erin "echo erinpw | sudo -S -u root -g adm id"
  expect_rc 1
  expect_out_empty
  expect_err_has "erin $NOT_ALLOWED"
  end
}

begin frank-exact-args-allowed && {
  run frank "sudo -n cat /etc/hostname"
  expect_rc 0
  expect_out_line "$(cat /etc/hostname)"
  end
}

begin frank-other-args-denied && {
  run frank "echo frankpw | sudo -S cat /etc/shadow"
  expect_rc 1
  expect_out_empty
  expect_err_has "frank $NOT_ALLOWED"
  end
}

begin frank-no-args-for-exact-rule-denied && {
  run frank "echo frankpw | sudo -S cat"
  expect_rc 1
  expect_err_has "frank $NOT_ALLOWED"
  end
}

begin frank-glob-args-allowed && {
  run frank "sudo -n ls /tmp/frankfile"
  expect_rc 0
  expect_out_line /tmp/frankfile
  end
}

begin frank-glob-args-denied && {
  run frank "echo frankpw | sudo -S ls /etc"
  expect_rc 1
  expect_out_empty
  expect_err_has "frank $NOT_ALLOWED"
  end
}

begin frank-empty-args-rule-allowed && {
  run frank "sudo -n true"
  expect_rc 0
  end
}

begin frank-empty-args-rule-with-args-denied && {
  run frank "echo frankpw | sudo -S true extra"
  expect_rc 1
  expect_err_has "frank $NOT_ALLOWED"
  end
}

begin unknown-runas-user && {
  run alice "echo alicepw | sudo -S -u nosuchuser id"
  expect_rc 1
  expect_out_empty
  expect_err_has 'unknown user nosuchuser'
  end
}

begin command-not-found && {

  run alice "echo alicepw | sudo -S nosuchcmd"
  expect_rc 1
  expect_out_empty
  expect_err_has 'nosuchcmd: command not found'
  end
}

begin chdir-option-not-permitted && {
  run alice "echo alicepw | sudo -S -D /tmp pwd"
  expect_rc 1
  expect_out_empty
  expect_err_has 'you are not permitted to use the -D option'
  end
}



begin exit-status-propagation && {
  run alice "echo alicepw | sudo -S sh -c 'exit 42'"
  expect_rc 42
  end
}

begin signal-death-propagation && {


  run alice "echo alicepw | sudo -S sh -c 'kill -TERM \$\$'; echo shell-saw=\$?"
  expect_rc 0
  expect_out_line shell-saw=143
  end
}



begin env-reset-drops-user-vars && {
  XENV=(FOO=bar)
  run alice "echo alicepw | sudo -S env"
  expect_rc 0
  expect_out_has SUDO_USER=alice
  expect_out_lacks FOO=bar
  end
}

begin env-secure-path && {
  run alice "PATH=/home/alice/bin:/usr/bin:/bin; echo alicepw | sudo -S env"
  expect_rc 0
  expect_out_line "PATH=$SECURE_PATH"
  end
}

begin env-sudo-variables && {
  run alice "echo alicepw | sudo -S env"
  expect_rc 0
  expect_out_line SUDO_USER=alice
  expect_out_line "SUDO_UID=$(uid_of alice)"
  expect_out_line "SUDO_GID=$(gid_of alice)"
  expect_out_line SUDO_COMMAND=/usr/bin/env
  end
}

begin env-sudo-command-with-args && {
  run alice "echo alicepw | sudo -S printenv SUDO_COMMAND"
  expect_rc 0
  expect_out_line '/usr/bin/printenv SUDO_COMMAND'
  end
}

begin env-target-identity && {
  run alice "echo alicepw | sudo -S env"
  expect_rc 0
  expect_out_line HOME=/root
  expect_out_line USER=root
  expect_out_line LOGNAME=root
  end
}

begin env-target-identity-other-user && {
  run alice "echo alicepw | sudo -S -u bob env"
  expect_rc 0
  expect_out_line HOME=/home/bob
  expect_out_line USER=bob
  expect_out_line SUDO_USER=alice
  end
}

begin env-ld-preload-dropped && {


  XENV=(LD_PRELOAD=/nonexistent/libevil.so LD_LIBRARY_PATH=/tmp)
  run alice "echo alicepw | sudo -S env"
  expect_rc 0
  expect_out_lacks LD_PRELOAD
  expect_out_lacks LD_LIBRARY_PATH
  end
}

begin env-E-denied-without-setenv && {
  run carol "sudo -n -E id -u"
  expect_rc 1
  expect_out_empty
  expect_err_has 'you are not allowed to preserve the environment'
  end
}

begin env-var-arg-denied-without-setenv && {
  run carol "sudo -n FOO=bar id -u"
  expect_rc 1
  expect_out_empty
  expect_err_has 'you are not allowed to set the following environment variables: FOO'
  end
}

begin env-E-allowed-for-ALL-command && {

  XENV=(FOO=bar)
  run alice "echo alicepw | sudo -S -E env"
  expect_rc 0
  expect_out_line FOO=bar
  end
}

begin env-E-with-setenv-keeps-safe-vars && {
  XENV=(FOO=bar)
  run erin "sudo -n -E env"
  expect_rc 0
  expect_out_line FOO=bar
  expect_out_line USER=root
  expect_out_line SUDO_USER=erin
  expect_out_line "PATH=$SECURE_PATH"


  expect_out_line HOME=/home/erin
  end
}

begin env-E-still-drops-dangerous-vars && {

  XENV=(LD_PRELOAD=/nonexistent/libevil.so LD_FOO=1 BASH_ENV=/tmp/evil
        PYTHONPATH=/tmp/evil PERL5OPT=-d FOO=bar)

  run erin "exec env 'BASH_FUNC_evil%%=() { echo pwned; }' sudo -n -E env"
  expect_rc 0
  expect_out_line FOO=bar
  expect_out_lacks LD_PRELOAD
  expect_out_lacks LD_FOO
  expect_out_lacks BASH_ENV
  expect_out_lacks PYTHONPATH
  expect_out_lacks PERL5OPT
  expect_out_lacks BASH_FUNC
  end
}

begin env-var-arg-with-setenv && {
  run erin "sudo -n FOO=bar BAZ=qux env"
  expect_rc 0
  expect_out_line FOO=bar
  expect_out_line BAZ=qux
  end
}



begin list-alice && {
  run alice "echo alicepw | sudo -S -l"
  expect_rc 0
  expect_out_has 'User alice may run the following commands'
  expect_out_has '(ALL : ALL) ALL'
  end
}

begin list-carol && {

  run carol "sudo -n -l"
  expect_rc 0
  expect_out_has '/usr/bin/id'
  expect_out_has '/usr/bin/whoami'
  expect_out_has 'NOPASSWD'
  expect_out_has '(bob)'
  end
}

begin list-carol-command && {
  run carol "sudo -n -l /usr/bin/id"
  expect_rc 0
  expect_out_line /usr/bin/id
  end
}

begin list-carol-command-path-search && {
  run carol "sudo -n -l id"
  expect_rc 0
  expect_out_line /usr/bin/id
  end
}

begin list-carol-command-denied && {
  run carol "sudo -n -l /usr/bin/cat"
  expect_rc 1
  expect_out_empty
  end
}



begin tty-prompt-and-no-echo && {
  pty alice "sudo id -u" -e '\[sudo\] password for alice: ' -s 'alicepw\r'
  expect_rc 0
  expect_out_has '[sudo] password for alice:'
  expect_out_line 0
  expect_out_lacks alicepw
  end
}

begin tty-wrong-then-right && {
  pty alice "sudo id -u" -e 'password for alice: ' -s 'wrong\r' \
                         -e 'password for alice: ' -s 'alicepw\r'
  expect_rc 0
  expect_out_has 'Sorry, try again.'
  expect_out_line 0
  expect_out_lacks wrong
  end
}

begin tty-no-password-required-for-nopasswd && {
  pty carol "sudo id -u"
  expect_rc 0
  expect_out_line 0
  expect_out_lacks 'password for'
  end
}

begin tty-validate-then-noninteractive && {
  pty alice "sudo -v && sudo -n id -u" -e 'password for alice: ' -s 'alicepw\r'
  expect_rc 0
  expect_out_line 0
  end
}

begin tty-timestamp-reused-without-prompt && {
  pty alice "sudo id -u && sudo id -un" -e 'password for alice: ' -s 'alicepw\r'
  expect_rc 0
  expect_out_line 0
  expect_out_line root
  [[ $(grep -c 'password for alice' <<<"$OUT") == 1 ]] || fail "expected exactly one password prompt"
  end
}

begin tty-k-invalidates && {
  pty alice "sudo -v && sudo -k && sudo -n true; echo after-k=\$?" \
      -e 'password for alice: ' -s 'alicepw\r'
  expect_rc 0
  expect_out_line after-k=1
  expect_out_has "$PW_REQUIRED"
  end
}

begin tty-K-removes && {
  pty alice "sudo -v && sudo -K && sudo -n true; echo after-K=\$?" \
      -e 'password for alice: ' -s 'alicepw\r'
  expect_rc 0
  expect_out_line after-K=1
  expect_out_has "$PW_REQUIRED"
  end
}

begin tty-timestamp-is-per-tty && {
  pty alice "sudo -v && echo validated" -e 'password for alice: ' -s 'alicepw\r'
  expect_rc 0
  expect_out_line validated

  pty alice "sudo -n true; echo second-session=\$?"
  expect_rc 0
  expect_out_line second-session=1
  expect_out_has "$PW_REQUIRED"
  end
}



begin login-shell-i && {
  run alice "echo alicepw | sudo -S -i pwd && echo alicepw | sudo -S -i printenv HOME"
  expect_rc 0
  expect_out_line /root
  [[ $(grep -cx /root <<<"$OUT") == 2 ]] || fail "stdout: expected '/root' twice (cwd and HOME)"
  end
}

begin login-shell-i-is-login-shell && {

  run alice "echo alicepw | sudo -S -i shopt -q login_shell"
  expect_rc 0
  end
}

begin shell-s-runs-SHELL && {

  run alice "printf 'alicepw\n' | SHELL=/bin/bash sudo -S -s declare -p BASH BASH_EXECUTION_STRING"
  expect_rc 0
  expect_out_line 'declare -- BASH="/bin/bash"'
  expect_out_line 'declare -- BASH_EXECUTION_STRING="declare -p BASH BASH_EXECUTION_STRING"'
  end
}

begin shell-s-interactive && {
  pty alice "SHELL=/bin/bash sudo -k -s" \
    -e 'password for alice:' -s 'alicepw\r' -e '# ' \
    -s 'echo shell:$BASH interactive:$-\r' -e 'shell:/bin/bash interactive:' \
    -s 'exit\r'
  expect_rc 0
  [[ $OUT =~ shell:/bin/bash\ interactive:[a-zA-Z]*i ]] || fail 'sudo -s did not start interactive bash'
  end
}



begin help-exit-0 && {
  run alice "sudo -h"
  expect_rc 0
  expect_out_has 'usage: sudo'
  end
}

begin version-exit-0 && {
  run alice "sudo -V"
  expect_rc 0
  expect_out_has 'version'
  end
}

begin usage-error-no-args && {
  run alice "sudo"
  expect_rc 1
  expect_err_has 'usage: sudo'
  end
}



begin sudoers-syntax-error-reported && {




  printf 'this is not valid sudoers\n' >/etc/sudoers.d/zz-bad
  chmod 0440 /etc/sudoers.d/zz-bad
  run alice "echo alicepw | sudo -S id -u"
  expect_err_match 'syntax error|parse error'
  if [[ $RC == 0 ]]; then expect_out_line 0; else expect_rc 1; expect_out_empty; fi
  end
}

begin sudoers-main-syntax-error-reported && {

  echo 'garbage here' >>/etc/sudoers
  run carol "sudo -n id -u"
  expect_err_match 'syntax error|parse error'
  if [[ $RC == 0 ]]; then expect_out_line 0; else expect_rc 1; expect_out_empty; fi
  end
}

begin sudoers-world-writable-include-ignored && {



  printf 'bob ALL=(ALL) NOPASSWD: ALL\n' >/etc/sudoers.d/zz-ww
  chmod 0666 /etc/sudoers.d/zz-ww
  run bob "sudo -n id -u"
  expect_rc 1
  expect_out_empty
  expect_err_has 'is world writable'
  end
}

begin sudoers-group-writable-nonroot-group-ignored && {


  printf 'bob ALL=(ALL) NOPASSWD: ALL\n' >/etc/sudoers.d/zz-gw
  chgrp bob /etc/sudoers.d/zz-gw
  chmod 0460 /etc/sudoers.d/zz-gw
  run bob "sudo -n id -u"
  expect_rc 1
  expect_out_empty
  expect_err_match 'gid|group|writable'
  end
}

begin sudoers-include-owned-by-nonroot-ignored && {

  printf 'bob ALL=(ALL) NOPASSWD: ALL\n' >/etc/sudoers.d/zz-own
  chown bob:root /etc/sudoers.d/zz-own
  chmod 0440 /etc/sudoers.d/zz-own
  run bob "sudo -n id -u"
  expect_rc 1
  expect_out_empty
  expect_err_has "is owned by uid $(uid_of bob), should be 0"
  end
}

begin sudoers-world-writable-refused && {
  chmod 0446 /etc/sudoers
  run carol "sudo -n id -u"
  expect_rc 1
  expect_out_empty
  expect_err_has '/etc/sudoers is world writable'
  end
}

begin sudoers-owned-by-nonroot-refused && {
  chown bob /etc/sudoers
  run carol "sudo -n id -u"
  expect_rc 1
  expect_out_empty
  expect_err_has "/etc/sudoers is owned by uid $(uid_of bob), should be 0"
  end
}

begin sudoers-include-dir-world-writable-ignored && {



  chmod 0777 /etc/sudoers.d
  run carol "sudo -n id -u"
  expect_rc 1
  expect_out_empty
  expect_err_has 'is world writable'
  end
}



begin binary-without-setuid-bit && {



  install -o root -g root -m 0755 /usr/bin/sudo /tmp/sudo-nosuid
  run alice "/tmp/sudo-nosuid -n true"
  expect_rc 1
  expect_out_empty
  expect_err_match 'effective uid is not 0|must be owned by uid 0 and have the setuid bit set'
  rm -f /tmp/sudo-nosuid
  end
}



edit_setup() {
  rm -f /etc/henryfile /etc/henrynew /etc/henrylink
  printf 'original\n' >/etc/henryfile
  chmod 0644 /etc/henryfile
  cat >/usr/local/bin/henry-editor <<'EOF'
#!/bin/sh
test "$(id -u)" = "$(id -u henry)" || exit 90
test "$(stat -c %u "$1")" = "$(id -u henry)" || exit 91
test "$(stat -c %a "$1")" = 600 || exit 92
printf 'edited\n' >>"$1"
EOF
  chmod 0755 /usr/local/bin/henry-editor
}

begin sudoedit-edits-as-invoker-preserves-root-owner && {
  edit_setup
  run henry 'SUDO_EDITOR=/usr/local/bin/henry-editor sudoedit -n /etc/henryfile'
  expect_rc 0
  [[ $(cat /etc/henryfile) == $'original\nedited' ]] || fail "edited contents missing"
  [[ $(stat -c %u:%g:%a /etc/henryfile) == 0:0:644 ]] || fail "original ownership/mode changed"
  end
}

begin sudoedit-unchanged-message && {
  edit_setup
  run henry 'SUDO_EDITOR=/usr/bin/true sudoedit -n /etc/henryfile'
  expect_rc 0
  expect_err_has 'sudoedit: /etc/henryfile unchanged'
  [[ $(cat /etc/henryfile) == original ]] || fail "unchanged original modified"
  end
}

begin sudoedit-refuses-symlink && {
  edit_setup
  ln -s /etc/henryfile /etc/henrylink
  run henry 'SUDO_EDITOR=/usr/local/bin/henry-editor sudoedit -n /etc/henrylink'
  expect_rc 1
  expect_err_has '/etc/henrylink: editing symbolic links is not permitted'
  [[ $(cat /etc/henryfile) == original ]] || fail "symlink target modified"
  end
}

begin sudoedit-refuses-user-writable-directory && {
  edit_setup
  mkdir -p /home/henry/unsafe
  chown henry:henry /home/henry/unsafe
  printf 'original\n' >/home/henry/unsafe/file
  run henry 'SUDO_EDITOR=/usr/local/bin/henry-editor sudoedit -n /home/henry/unsafe/file'
  expect_rc 1
  expect_err_has 'editing files in a writable directory is not permitted'
  [[ $(cat /home/henry/unsafe/file) == original ]] || fail "unsafe file modified"
  end
}

begin sudoedit-denies-unlisted-file && {
  edit_setup
  run henry "printf 'henrypw\n' | SUDO_EDITOR=/usr/bin/true sudoedit -S /etc/hostname"
  expect_rc 1
  expect_err_has "Sorry, user henry is not allowed to execute 'sudoedit /etc/hostname' as root"
  end
}

begin sudoedit-sudo-e-form && {
  edit_setup
  run henry 'EDITOR=/usr/local/bin/henry-editor sudo -n -e /etc/henryfile'
  expect_rc 0
  [[ $(cat /etc/henryfile) == $'original\nedited' ]] || fail "sudo -e did not edit"
  end
}

begin sudoedit-creates-new-file && {
  edit_setup
  run henry 'SUDO_EDITOR=/usr/local/bin/henry-editor sudoedit -n /etc/henrynew'
  expect_rc 0
  [[ $(cat /etc/henrynew) == edited ]] || fail "new file contents missing"
  [[ $(stat -c %u:%g:%a /etc/henrynew) == 0:0:644 ]] || fail "new file ownership/mode incorrect"
  end
}

begin sudoedit-editor-path-lookup && {
  edit_setup
  run henry 'SUDO_EDITOR=henry-editor sudoedit -n /etc/henryfile'
  expect_rc 0
  [[ $(cat /etc/henryfile) == $'original\nedited' ]] || fail "PATH editor did not edit"
  end
}

begin sudoedit-editor-failure-status && {
  edit_setup
  run henry 'SUDO_EDITOR=/usr/bin/false sudoedit -n /etc/henryfile'
  expect_rc 1
  [[ $(cat /etc/henryfile) == original ]] || fail "failed editor changed original"
  end
}

begin sudoedit-refuses-nonregular-file && {
  edit_setup
  mkdir -p /etc/henrydir
  run henry 'SUDO_EDITOR=/usr/bin/true sudoedit -n /etc/henrydir'
  expect_rc 1
  expect_err_has '/etc/henrydir: not a regular file'
  end
}

begin sudoedit-refuses-replaced-temp-symlink && {
  edit_setup
  cat >/usr/local/bin/henry-editor <<'EOF'
#!/bin/sh
rm -f "$1"
ln -s /etc/hostname "$1"
EOF
  run henry 'SUDO_EDITOR=/usr/local/bin/henry-editor sudoedit -n /etc/henryfile'
  expect_rc 1
  [[ $(cat /etc/henryfile) == original ]] || fail "unsafe temporary file copied back"
  end
}

begin sudoedit-rejects-editor-file-injection && {
  edit_setup
  run henry 'SUDO_EDITOR="/usr/bin/true -- /etc/hostname" sudoedit -n /etc/henryfile'
  expect_rc 1
  [[ $(cat /etc/henryfile) == original ]] || fail "injected editor changed original"
  end
}

begin sudoedit-writeback-as-target-retains-edits-on-error && {
  edit_setup
  run henry 'SUDO_EDITOR=/usr/local/bin/henry-editor sudoedit -n -u gina /etc/henryfile'
  expect_rc 1
  expect_err_has 'Permission denied'
  expect_err_has 'contents of edit session left in '
  [[ $(cat /etc/henryfile) == original ]] || fail "writeback failure damaged original"
  saved=$(printf '%s\n' "$ERR" | sed -n 's/^.*contents of edit session left in //p')
  [[ -f $saved && $(cat "$saved") == $'original\nedited' ]] || fail "edited temporary contents not retained"
  [[ -z $saved ]] || rm -f "$saved"
  end
}

begin sudoedit-refuses-itself-as-editor && {
  edit_setup
  run henry 'SUDO_EDITOR=/usr/bin/sudoedit sudoedit -n /etc/henryfile'
  expect_rc 1
  [[ $(cat /etc/henryfile) == original ]] || fail "recursive editor modified original"
  end
}

begin sudoedit-refuses-owned-directory-without-write-bit && {
  edit_setup
  mkdir -p /etc/henryowned
  printf 'original\n' >/etc/henryowned/file
  chown henry:henry /etc/henryowned
  chmod 0555 /etc/henryowned
  run henry 'SUDO_EDITOR=/usr/local/bin/henry-editor sudoedit -n /etc/henryowned/file'
  expect_rc 1
  expect_err_has 'editing files in a writable directory is not permitted'
  [[ $(cat /etc/henryowned/file) == original ]] || fail "owned-directory file modified"
  end
}




begin exec-symlink-swap-during-prompt && {


  run carol 'mkdir -p ~/x; printf "#!/bin/sh\necho pwned\n" > ~/evil; chmod +x ~/evil; ln -sf /usr/bin/id ~/x/id; ( sleep 1; echo carolpw ) | sudo -S -u bob ~/x/id & pid=$!; sleep 0.4; ln -sfn ~/evil ~/x/id; wait "$pid"'
  expect_err_has '[sudo] password for carol:'

  if [[ $RC == 0 ]]; then
    expect_out_has "uid=$(uid_of bob)(bob)"
  else
    expect_rc 1
    expect_out_empty
    expect_err_has 'not allowed to execute'
  fi
  expect_out_lacks pwned
  end
}

begin requiretty-refuses-unrelated-stdin-pty && {
  printf 'Defaults:carol requiretty\n' >/etc/sudoers.d/zz-requiretty
  chmod 0440 /etc/sudoers.d/zz-requiretty


  cat >"$WORK/no-controlling-tty.py" <<'EOF'
import os
import pty
import subprocess
import sys

master, slave = pty.openpty()
try:
    result = subprocess.run(
        ["sudo", "-n", "id", "-u"], stdin=slave, start_new_session=True
    )
finally:
    os.close(slave)
    os.close(master)
sys.exit(result.returncode)
EOF
  run carol "python3 '$WORK/no-controlling-tty.py'"
  expect_rc 1
  expect_out_empty
  expect_err_has 'sorry, you must have a tty to run sudo'
  end
}








for f in "$(dirname "$0")"/tests.d/*.sh; do
  [[ -f $f ]] && . "$f"
done





emit "1..$NUM"
emit "# implementation: $LABEL ($IMPL_BIN)"
emit "# passed: $PASSED/$NUM, failed: $FAILED"
for n in "${FAILED_NAMES[@]}"; do emit "# FAILED: $n"; done
reset_state
rm -rf "$WORK"
[[ $NUM -gt 0 ]] || { echo "# no tests matched filter '$FILTER'"; exit 2; }
[[ $FAILED -eq 0 ]]
