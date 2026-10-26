#!/usr/bin/env bash



set -euo pipefail
here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
root=$(dirname "$here")
case $(uname -m) in
  arm64|aarch64) native=arm64 ;;
  x86_64|amd64) native=amd64 ;;
  *) echo "unsupported host architecture" >&2; exit 2 ;;
esac
arch=$native
if [[ ${1:-} == --arch && $# == 2 ]]; then arch=$2; shift 2; fi
[[ $# == 0 && $arch =~ ^(amd64|arm64)$ ]] || {
  echo "usage: $0 [--arch amd64|arm64]" >&2; exit 2;
}
dest="$root/.lake/linux-$arch"
mkdir -p "$dest" "$here/out"
log="$here/out/linux-build-$arch.log"
builder=(docker build)
cache=()
if [[ -n ${SUDO_BUILD_CACHE:-} ]]; then
  builder=(docker buildx build)
  if [[ -f $SUDO_BUILD_CACHE/index.json ]]; then
    cache+=(--cache-from "type=local,src=$SUDO_BUILD_CACHE")
  fi
  cache+=(--cache-to "type=local,dest=$SUDO_BUILD_CACHE-new,mode=max")
fi
DOCKER_BUILDKIT=1 "${builder[@]}" "${cache[@]}" --platform "linux/$arch" \
  --build-arg "BASE=${SUDO_IT_BASE:-ubuntu:26.04}" \
  -t "lean-sudo-build:$arch" \
  -f "$here/Dockerfile.build" --target artifact \
  --output "type=local,dest=$dest" "$root" >"$log" 2>&1 \
  || { cat "$log" >&2; exit 2; }
if [[ $arch == "$native" ]]; then
  mkdir -p "$root/.lake/linux"
  cp "$dest/sudo" "$dest/visudo" "$root/.lake/linux/"
fi
echo "$dest/sudo"
echo "$dest/visudo"
