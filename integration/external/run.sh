#!/usr/bin/env bash
set -euo pipefail
here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
root=$(cd "$here/../.." && pwd)
implementations=(reference lean)
if [[ ${1:-} == --lean-only ]]; then implementations=(lean); shift; fi
[[ $# -le 1 ]] || {
  echo "usage: $0 [--lean-only] [Linux-binary-directory]" >&2
  exit 2
}
binaries=${1:-$root/.lake/linux}
for binary in sudo visudo; do
  [[ -f $binaries/$binary ]] || { echo "missing $binaries/$binary" >&2; exit 2; }
done
out=${SUDO_EXTERNAL_OUT:-$root/integration/out/external}
mkdir -p "$out" "$root/integration/out"
out=$(cd "$out" && pwd)
if [[ ${implementations[*]} == lean ]]; then
  [[ -f $out/reference.results.json ]] || {
    echo "--lean-only requires completed reference results in $out" >&2
    exit 2
  }
fi
lock="$root/integration/out/external.lock"
mkdir "$lock" 2>/dev/null || { echo "external suite already running: $lock" >&2; exit 2; }
context=$(mktemp -d)
cleanup() {
  rm -rf "$context"
  rmdir "$lock"
}
trap cleanup EXIT
cp "$binaries/sudo" "$binaries/visudo" "$context/"
cp "$here/Dockerfile.fixture" "$context/Dockerfile"
runner=lean-sudo-external-runner
reference=lean-sudo-external-reference
lean=lean-sudo-external-lean
if [[ ${implementations[*]} != lean ]]; then
  docker build --target reference -t "$reference" "$context" \
    >"$out/reference-build.log" 2>&1 || { cat "$out/reference-build.log" >&2; exit 2; }
fi
docker build --target lean -t "$lean" "$context" \
  >"$out/lean-build.log" 2>&1 || { cat "$out/lean-build.log" >&2; exit 2; }
docker build -f "$here/Dockerfile.runner" -t "$runner" "$here" \
  >"$out/runner-build.log" 2>&1 || { cat "$out/runner-build.log" >&2; exit 2; }
for implementation in "${implementations[@]}"; do
  fixture=$reference
  [[ $implementation != lean ]] || fixture=$lean
  docker run --rm --network none \
    -v "${SUDO_EXTERNAL_SOCKET:-/var/run/docker.sock}:/var/run/docker.sock" \
    -v "$out:/out" -e "FIXTURE_IMAGE=$fixture" -e "IMPLEMENTATION=$implementation" \
    -e "SUITE_THREADS=${SUDO_EXTERNAL_THREADS:-4}" \
    -e "CASE_TIMEOUT=${SUDO_EXTERNAL_TIMEOUT:-120}" "$runner"
done
docker run --rm --network none --entrypoint python3 -v "$out:/out" \
  "$runner" /opt/external/compare.py /out
