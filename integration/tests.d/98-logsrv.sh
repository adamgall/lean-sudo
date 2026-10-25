#!/bin/bash

logsrv_policy() {
  printf 'Defaults !requiretty, !authenticate, log_server_timeout=2\nDefaults log_servers="%s"\n%s\nalice ALL=(ALL:ALL) NOPASSWD: ALL\n' "$1" "${2:-}" >/etc/sudoers.d/98-logsrv
  chmod 0440 /etc/sudoers.d/98-logsrv
}
logsrv_start() {
  local tls=${1:-} peer=${2:-false} san=${3:-DNS:localhost,IP:127.0.0.1} cn=${4:-localhost}
  LSRV="$WORK/logsrv-$NUM"
  mkdir -p "$LSRV/io"
  cat >"$LSRV/server.conf" <<EOF
[server]
listen_address = 127.0.0.1:30343$tls
pid_file = $LSRV/pid
server_log = $LSRV/server.log
timeout = 5
EOF
  if [[ -n $tls ]]; then
    openssl req -x509 -newkey rsa:2048 -nodes -days 1 -subj /CN=LogSrv-Test-CA -addext basicConstraints=critical,CA:TRUE -addext keyUsage=critical,keyCertSign,cRLSign -keyout "$LSRV/ca.key" -out "$LSRV/ca.pem" >/dev/null 2>&1
    openssl req -new -newkey rsa:2048 -nodes -subj "/CN=$cn" -keyout "$LSRV/server.key" -out "$LSRV/server.csr" >/dev/null 2>&1
    printf 'basicConstraints=critical,CA:FALSE\nkeyUsage=critical,digitalSignature,keyEncipherment\nsubjectAltName=%s\nextendedKeyUsage=serverAuth,clientAuth\n' "$san" >"$LSRV/extensions"
    openssl x509 -req -in "$LSRV/server.csr" -CA "$LSRV/ca.pem" -CAkey "$LSRV/ca.key" -CAcreateserial -days 1 -extfile "$LSRV/extensions" -out "$LSRV/server.pem" >/dev/null 2>&1
    cat >>"$LSRV/server.conf" <<EOF
tls_cacert = $LSRV/ca.pem
tls_cert = $LSRV/server.pem
tls_key = $LSRV/server.key
tls_checkpeer = $peer
EOF
  fi
  cat >>"$LSRV/server.conf" <<EOF
[iolog]
iolog_dir = $LSRV/io
iolog_compress = false
iolog_flush = true
[eventlog]
log_type = logfile
log_format = json
log_exit = true
[logfile]
path = $LSRV/events.json
EOF
  logsrv_launch
}
logsrv_launch() {

  /usr/sbin/sudo_logsrvd -f "$LSRV/server.conf" -n >"$LSRV/daemon.out" 2>&1 &
  LSRV_PID=$!
  for _ in {1..50}; do
    python3 -c 'import socket; socket.create_connection(("127.0.0.1",30343),.05).close()' 2>/dev/null && return 0
    kill -0 "$LSRV_PID" 2>/dev/null || break
    sleep .05
  done
  fail "sudo_logsrvd failed to start: $(cat "$LSRV/daemon.out")"
  return 1
}
logsrv_stop() {

  sleep .1
  kill "$LSRV_PID" 2>/dev/null || true
  wait "$LSRV_PID" 2>/dev/null || true


  python3 - "$LSRV" "$OUTDIR/$LABEL-$CUR.json" <<'PY'
import json,pathlib,sys
root=pathlib.Path(sys.argv[1])
volatile={"uuid","server_time","submit_time","alert_time","exit_time","run_time","iolog_path","peeraddr","timestamp","iolog_offset"}
def stable(value):
    if isinstance(value,dict):
        return {k:stable(v) for k,v in value.items() if k not in volatile}
    if isinstance(value,list):
        return [stable(v) for v in value]
    return value
events=stable(json.loads((root/"events.json").read_text())) if (root/"events.json").exists() and (root/"events.json").stat().st_size else {}
for event in events.values():
    for key in ("runenv","submitenv"):
        if key in event: event[key]=sorted(event[key])
streams={}
for file in sorted((root/"io").rglob("*")):
    if file.name in ("stdin","stdout","stderr","ttyin","ttyout"):
        streams[str(file.relative_to(root/"io"))]=file.read_bytes().hex()
    elif file.name=="timing":
        records=[]
        for line in file.read_text().splitlines():
            parts=line.split()
            if not parts: continue
            record=[parts[0]]+parts[2:]
            if records and record[0] in ("0","1","2","3","4") and records[-1][0]==record[0]:
                records[-1][1]=str(int(records[-1][1])+int(record[1]))
            else:
                records.append(record)
        streams[str(file.relative_to(root/"io"))]=[" ".join(record) for record in records]
pathlib.Path(sys.argv[2]).write_text(json.dumps({"events":events,"streams":streams},sort_keys=True,indent=2)+"\n")
PY
  [[ $? == 0 ]] || fail 'could not snapshot daemon records'
}
logsrv_event() {
  python3 -c 'import json,sys; d=json.load(open(sys.argv[1])); events=d if isinstance(d,list) else [d]; assert any(sys.argv[2] in e for e in events), events' "$LSRV/events.json" "$1" || fail "missing remote $1 event"
}
logsrv_io() {
  python3 -c 'import pathlib,sys,json; p=pathlib.Path(sys.argv[1]); fs=list(p.rglob("stdout")); assert len(fs)==1,fs; assert fs[0].read_bytes()==b"remote-output\n",fs[0].read_bytes(); meta=json.loads((fs[0].parent/"log.json").read_text()); assert meta["submituser"]=="alice",meta; assert (fs[0].parent/"timing").stat().st_mode & 0o222 == 0' "$LSRV/io" || fail 'remote I/O data, metadata or final commit is incorrect'
}

begin logsrv-unreachable-event-default-continues && {
  logsrv_policy 127.0.0.1:30342
  run alice 'sudo -n /bin/echo remote-output'
  expect_rc 0
  expect_out_line remote-output
  expect_err_has 'unable to connect to log server'
  end
}
begin logsrv-unreachable-event-required-refuses && {
  logsrv_policy 127.0.0.1:30342 'Defaults !ignore_logfile_errors'
  run alice 'sudo -n /bin/echo remote-output'
  expect_rc 1
  expect_out_empty
  expect_err_has 'unable to connect to log server'
  end
}
begin logsrv-unreachable-iolog-refuses && {
  logsrv_policy 127.0.0.1:30342 'Defaults log_output'
  run alice 'sudo -n /bin/echo remote-output'
  expect_rc 1
  expect_out_empty
  expect_err_has 'unable to connect to log server'
  end
}
begin logsrv-unreachable-iolog-ignore-continues && {
  logsrv_policy 127.0.0.1:30342 'Defaults log_output, ignore_iolog_errors'
  run alice 'sudo -n /bin/echo remote-output'
  expect_rc 0
  expect_out_line remote-output
  expect_err_has 'unable to connect to log server'
  end
}
begin logsrv-tcp-accept-without-iolog-no-exit && {
  logsrv_start
  logsrv_policy 127.0.0.1:30343 'Defaults !ignore_logfile_errors, log_exit_status'
  run alice 'sudo -n /bin/echo remote-output'
  expect_rc 0
  expect_out_line remote-output
  logsrv_stop
  logsrv_event accept

  python3 -c 'import json,sys; assert "exit" not in json.load(open(sys.argv[1]))' "$LSRV/events.json" || fail 'unexpected remote exit without I/O logging'
  end
}
begin logsrv-tcp-reject && {
  logsrv_start
  logsrv_policy 127.0.0.1:30343
  run bob 'sudo -n /bin/echo remote-output'
  expect_rc 1
  expect_out_empty
  logsrv_stop
  logsrv_event reject
  end
}
begin logsrv-tcp-iolog && {
  logsrv_start
  logsrv_policy 127.0.0.1:30343 'Defaults log_output'
  run alice 'sudo -n /bin/echo remote-output'
  expect_rc 0
  expect_out_line remote-output
  logsrv_stop
  logsrv_io
  logsrv_event accept
  logsrv_event exit
  end
}
begin logsrv-server-list-failover && {
  logsrv_start
  logsrv_policy '127.0.0.1:30342 127.0.0.1:30343' 'Defaults log_output'
  run alice 'sudo -n /bin/echo remote-output'
  expect_rc 0
  expect_out_line remote-output
  logsrv_stop
  logsrv_io
  end
}
begin logsrv-tls-verified-iolog && {
  logsrv_start '(tls)'
  logsrv_policy '127.0.0.1:30343(tls)' "Defaults log_output, log_server_cabundle=\"$LSRV/ca.pem\""
  run alice 'sudo -n /bin/echo remote-output'
  expect_rc 0
  expect_out_line remote-output
  logsrv_stop
  logsrv_io
  end
}
begin logsrv-tls-mutual-certificate && {
  logsrv_start '(tls)' true
  logsrv_policy 'localhost:30343(tls)' "Defaults log_output, log_server_cabundle=\"$LSRV/ca.pem\", log_server_peer_cert=\"$LSRV/server.pem\", log_server_peer_key=\"$LSRV/server.key\""
  run alice 'sudo -n /bin/echo remote-output'
  expect_rc 0
  expect_out_line remote-output
  logsrv_stop
  logsrv_io
  end
}
begin logsrv-tls-untrusted-refuses && {
  logsrv_start '(tls)'
  logsrv_policy '127.0.0.1:30343(tls)' 'Defaults log_output'
  run alice 'sudo -n /bin/echo remote-output'
  expect_rc 1
  expect_out_empty
  expect_err_has 'TLS connection to 127.0.0.1:30343 failed: certificate verify failed'
  expect_err_has 'TLS handshake was unsuccessful: Success'
  logsrv_stop
  end
}
begin logsrv-tls-verification-disabled && {
  logsrv_start '(tls)'
  logsrv_policy '127.0.0.1:30343(tls)' 'Defaults log_output, !log_server_verify, log_server_cabundle="/no-such-ca"'
  run alice 'sudo -n /bin/echo remote-output'
  expect_rc 0
  expect_out_line remote-output
  logsrv_stop
  logsrv_io
  end
}

begin logsrv-tcp-empty-iolog-final-commit && {
  logsrv_start
  logsrv_policy 127.0.0.1:30343 'Defaults log_output'
  run alice 'sudo -n /bin/true'
  expect_rc 0
  logsrv_stop
  logsrv_event accept
  logsrv_event exit
  python3 -c 'import pathlib,sys; fs=list(pathlib.Path(sys.argv[1]).rglob("timing")); assert len(fs)==1; assert fs[0].stat().st_mode & 0o222 == 0' "$LSRV/io" || fail 'empty log not committed'
  end
}
begin logsrv-tcp-input-and-error-streams && {
  logsrv_start
  logsrv_policy 127.0.0.1:30343 'Defaults log_input, log_output'
  run alice "printf 'input-data\\n' | sudo -n /bin/sh -c 'cat; echo error-data >&2'"
  expect_rc 0
  expect_out_line input-data
  expect_err_has error-data
  logsrv_stop
  python3 -c 'import pathlib,sys; fs=list(pathlib.Path(sys.argv[1]).rglob("stdin")); assert len(fs)==1; p=fs[0].parent; assert fs[0].read_bytes()==b"input-data\n"; assert (p/"stdout").read_bytes()==b"input-data\n"; assert (p/"stderr").read_bytes()==b"error-data\n"' "$LSRV/io" || fail 'remote stdin/stdout/stderr mismatch'
  end
}
begin logsrv-tcp-requiretty-alert && {
  logsrv_start
  logsrv_policy 127.0.0.1:30343 'Defaults requiretty'
  run alice 'sudo -n /bin/echo remote-output'
  expect_rc 1
  expect_out_empty
  logsrv_stop
  logsrv_event alert
  end
}

begin logsrv-tls-identity-mismatch-refuses && {
  logsrv_start '(tls)' false DNS:wronghost.invalid
  logsrv_policy '127.0.0.1:30343(tls)' "Defaults log_output, log_server_cabundle=\"$LSRV/ca.pem\""
  run alice 'sudo -n /bin/echo remote-output'
  expect_rc 1
  expect_out_empty
  expect_err_has 'TLS connection to 127.0.0.1:30343 failed: certificate verify failed'
  expect_err_has 'TLS handshake was unsuccessful: Success'
  logsrv_stop
  end
}
begin logsrv-tls-hostname-matches-peer-address && {
  logsrv_start '(tls)' false IP:127.0.0.1 wronghost.invalid
  logsrv_policy 'localhost:30343(tls)' "Defaults log_output, log_server_cabundle=\"$LSRV/ca.pem\""
  run alice 'sudo -n /bin/echo remote-output'
  expect_rc 0
  expect_out_line remote-output
  logsrv_stop
  logsrv_io
  end
}

begin logsrv-tcp-subcommands-serialized-with-iolog && {
  logsrv_start
  logsrv_policy 127.0.0.1:30343 'Defaults log_output, log_subcmds, intercept_type=trace'
  run alice "sudo -n /bin/sh -c '/usr/bin/printf \"remote-output\\n\"'"
  expect_rc 0
  expect_out_line remote-output
  logsrv_stop
  logsrv_io
  python3 -c 'import pathlib,sys; s=pathlib.Path(sys.argv[1]).read_text(); assert s.count("\"accept\"")>=2; assert "/usr/bin/printf" in s' "$LSRV/events.json" || fail 'missing remote subcommand accept'
  end
}
begin logsrv-tcp-intercept-rejection-serialized && {
  logsrv_start
  logsrv_policy 127.0.0.1:30343 'Defaults log_output, intercept, intercept_type=trace'
  printf 'alice ALL=(ALL:ALL) NOPASSWD: !/usr/bin/true\n' >>/etc/sudoers.d/98-logsrv
  run alice "sudo -n /bin/sh -c '/usr/bin/true; echo remote-output'"
  expect_rc 0
  expect_out_line remote-output
  logsrv_stop
  logsrv_event reject
  end
}

logsrv_disconnect_case() {
  local extra=
  [[ $1 == true ]] && extra=', ignore_iolog_errors'
  logsrv_start
  logsrv_policy 127.0.0.1:30343 "Defaults log_output$extra"
  LSRV_OLD_PID=$LSRV_PID
  (


    for _ in {1..100}; do
      if python3 -c 'import pathlib,sys; assert any(p.read_bytes()==b"before\n" for p in pathlib.Path(sys.argv[1]).rglob("stdout"))' "$LSRV/io" 2>/dev/null; then
        kill "$LSRV_OLD_PID" || exit 1
        sleep .2
        logsrv_launch || exit 1
        printf '%s\n' "$LSRV_PID" >"$LSRV/restarted-pid"
        exit 0
      fi
      sleep .02
    done
    exit 1
  ) &
  LSRV_CONTROLLER=$!
  run alice "sudo -n /bin/sh -c 'echo before; sleep 3; echo after; sleep 1; echo complete'"
  wait "$LSRV_CONTROLLER" || fail 'could not disconnect and restart the daemon'
  wait "$LSRV_OLD_PID" 2>/dev/null || true
  if [[ -s $LSRV/restarted-pid ]]; then
    LSRV_PID=$(cat "$LSRV/restarted-pid")
  else
    fail 'daemon restart was not recorded'
  fi
  python3 -c 'import json,pathlib,sys; pathlib.Path(sys.argv[1]).write_text(json.dumps({"status":int(sys.argv[2]),"stdout":sys.argv[3],"stderr":sys.argv[4]},sort_keys=True,indent=2)+"\n")' "$OUTDIR/$LABEL-$CUR-result.json" "$RC" "$OUT" "$ERR"
  expect_out_line before
  expect_err_has 'lost connection to log server'
  if [[ $1 == true ]]; then
    expect_rc 0
    expect_out_line after
    expect_out_line complete
    [[ $ERR == 'sudo: lost connection to log server' ]] || fail 'ignored disconnect diagnostic differs'
  else
    expect_rc 1
    [[ $OUT == before ]] || fail 'command continued after fatal log disconnect'
    [[ $ERR == $'sudo: lost connection to log server\nsudo: unexpected child termination condition: 0' ]] || fail 'fatal disconnect diagnostic differs'
  fi
  logsrv_stop
  logsrv_event accept
  python3 -c 'import json,pathlib,sys; root=pathlib.Path(sys.argv[1]); files=list((root/"io").rglob("stdout")); assert len(files)==1; assert files[0].read_bytes()==b"before\n"; assert (files[0].parent/"timing").stat().st_mode & 0o222; assert "exit" not in json.loads((root/"events.json").read_text())' "$LSRV" || fail 'disconnected log was resumed or incorrectly committed'
}
begin logsrv-tcp-disconnected-stream && {
  logsrv_disconnect_case false
  end
}
begin logsrv-tcp-disconnected-stream-ignored && {
  logsrv_disconnect_case true
  end
}

begin sudoedit-execution-logsrv && {
  sudoedit_parity_setup
  logsrv_start
  printf 'Defaults:henry log_servers="127.0.0.1:30343",log_server_timeout=2,log_output,!ignore_iolog_errors\n' >>/etc/sudoers.d/58-sudoedit
  cat >/usr/local/bin/henry-editor <<'EOF'
#!/bin/sh
printf 'remote-editor-output\n'
printf 'edited\n' >>"$1"
EOF
  run henry 'SUDO_EDITOR=/usr/local/bin/henry-editor sudoedit -n /etc/henryfile'
  expect_rc 0
  expect_out_line remote-editor-output
  [[ $(cat /etc/henryfile) == $'original\nedited' ]] || fail 'remote-logged editor did not copy back'
  logsrv_stop
  logsrv_event accept
  logsrv_event exit
  python3 - "$LSRV/io" <<'PY'
import json, pathlib, sys
files = list(pathlib.Path(sys.argv[1]).rglob('stdout'))
assert len(files) == 1, files
assert files[0].read_bytes() == b'remote-editor-output\n', files[0].read_bytes()
metadata = json.loads((files[0].parent / 'log.json').read_text())
assert metadata['submituser'] == 'henry', metadata
assert metadata['runargv'] == ['/usr/local/bin/henry-editor', '--', '/etc/henryfile'], metadata
assert (files[0].parent / 'timing').stat().st_mode & 0o222 == 0
PY
  [[ $? == 0 ]] || fail 'remote editor stream, metadata or final commit differs'
  run root "sudoreplay.ws -d '$LSRV/io' -l"
  expect_rc 0
  expect_out_has 'COMMAND=/usr/local/bin/henry-editor -- /etc/henryfile'
  end
}
