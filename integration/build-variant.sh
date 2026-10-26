#!/usr/bin/env bash
set -euo pipefail
here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
root=$(dirname "$here")
variant=${1:-sanitize}
case "$variant" in
  sanitize|asan|coverage) ;;
  *) echo 'expected sanitize|asan|coverage' >&2; exit 2 ;;
esac
[[ $# -le 1 ]] || exit 2
dest="$root/.lake/linux-$variant"
mkdir -p "$dest" "$here/out"
args=(--build-arg "BASE=${SUDO_IT_BASE:-ubuntu:26.04}" --build-arg "VARIANT=$variant")
DOCKER_BUILDKIT=1 docker build "${args[@]}" -f "$here/Dockerfile.build" \
  --target variant-artifact --output "type=local,dest=$dest" "$root" \
  >"$here/out/$variant-build.log" 2>&1 \
  || { cat "$here/out/$variant-build.log" >&2; exit 2; }
if [[ $variant == coverage ]]; then
  docker build "${args[@]}" -f "$here/Dockerfile.build" --target coverage-report \
    -t lean-sudo-coverage-report "$root" >>"$here/out/$variant-build.log" 2>&1 \
    || { cat "$here/out/$variant-build.log" >&2; exit 2; }
fi
printf '%s\n' "$dest/sudo" "$dest/visudo"
