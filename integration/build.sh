#!/usr/bin/env bash



set -euo pipefail
here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
root=$(dirname "$here")
dest="$root/.lake/linux"
mkdir -p "$dest" "$here/out"
DOCKER_BUILDKIT=1 docker build \
  --build-arg "BASE=${SUDO_IT_BASE:-ubuntu:26.04}" \
  -f "$here/Dockerfile.build" --target artifact \
  --output "type=local,dest=$dest" "$root" >"$here/out/linux-build.log" 2>&1 \
  || { tail -60 "$here/out/linux-build.log" >&2; exit 2; }
echo "$dest/sudo"
echo "$dest/visudo"
