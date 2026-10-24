#!/usr/bin/env bash
# Build lean-sudo's Linux `sudo` and `visudo` in a container (integration/Dockerfile.build)
# and copy them to .lake/linux/. Works on macOS (Docker Desktop/colima) and Linux.
# Environment: SUDO_IT_BASE (base image, default ubuntu:26.04).
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
