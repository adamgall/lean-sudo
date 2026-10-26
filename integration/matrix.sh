#!/usr/bin/env bash
set -euo pipefail
here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
root=$(dirname "$here")
arches=(amd64 arm64)
if [[ ${1:-} == --arch && $# == 2 && $2 =~ ^(amd64|arm64)$ ]]; then
  arches=("$2")
  shift 2
fi
[[ $# == 0 ]] || { echo "usage: $0 [--arch amd64|arm64]" >&2; exit 2; }
jobs=${SUDO_MATRIX_JOBS:-2}
[[ $jobs =~ ^[1-8]$ ]] || { echo 'SUDO_MATRIX_JOBS must be 1..8' >&2; exit 2; }
out="$here/out/matrix"
mkdir -p "$out"
for arch in "${arches[@]}"; do
  "$here/build.sh" --arch "$arch"
done
run_one() {
  local arch=$1 suite=$2 impl=$3 label="$1-$2-$3" binary rc=0
  local args=(--arch "$arch")
  [[ $suite == visudo ]] && args+=(--visudo)
  binary=reference
  [[ $impl == lean-sudo ]] && binary="$root/.lake/linux-$arch/$suite"
  SUDO_IT_OUT="$out" SUDO_IT_LABEL="$label" \
    "$here/run.sh" "${args[@]}" "$binary" >"$out/$label.stdout" 2>&1 || rc=$?
  printf '%s\n' "$rc" >"$out/$label.status"
}
pids=()
for arch in "${arches[@]}"; do
  for suite in sudo visudo; do
    for impl in lean-sudo reference; do
      run_one "$arch" "$suite" "$impl" &
      pids+=("$!")
      if [[ ${#pids[@]} -ge $jobs ]]; then
        for pid in "${pids[@]}"; do wait "$pid"; done
        pids=()
      fi
    done
  done
done
for pid in "${pids[@]}"; do wait "$pid"; done
python3 - "$out" "${arches[@]}" <<'PY'
import pathlib
import re
import sys
out = pathlib.Path(sys.argv[1])
failed = False
print('ARCH   SUITE   IMPLEMENTATION  PASS  FAIL  RESULT')
for arch in sys.argv[2:]:
    for suite in ('sudo', 'visudo'):
        counts = []
        for impl in ('lean-sudo', 'reference'):
            label = f'{arch}-{suite}-{impl}'
            tap = out / f'{label}.tap'
            text = tap.read_text() if tap.exists() else ''
            passed = len(re.findall(r'^ok \d+\b', text, re.M))
            errors = len(re.findall(r'^not ok \d+\b', text, re.M))
            plans = re.findall(r'^1\.\.(\d+)\s*$', text, re.M)
            complete = len(plans) == 1 and int(plans[0]) == passed + errors
            rc = int((out / f'{label}.status').read_text())
            good = rc == 0 and errors == 0 and passed > 0 and complete
            failed |= not good
            counts.append(passed)
            result = 'PASS' if good else 'FAIL'
            print(f'{arch:6} {suite:7} {impl:14} {passed:4} {errors:5}  {result}')
        if counts[0] != counts[1]:
            print(f'{arch} {suite}: implementation pass counts differ')
            failed = True
sys.exit(1 if failed else 0)
PY
