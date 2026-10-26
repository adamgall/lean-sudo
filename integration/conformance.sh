#!/usr/bin/env bash
set -euo pipefail
here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
root=$(dirname "$here")
sudo_binary=${CONFORMANCE_SUDO:-$root/.lake/linux/sudo}
visudo_binary=${CONFORMANCE_VISUDO:-$root/.lake/linux/visudo}
case $(uname -m) in
  arm64|aarch64) arch=arm64 ;;
  x86_64|amd64) arch=amd64 ;;
  *) echo 'unsupported architecture' >&2; exit 2 ;;
esac
image=${CONFORMANCE_IMAGE:-lean-sudo-it-$arch}
out=${CONFORMANCE_OUT:-$here/out}
mkdir -p "$out/conformance"
[[ -f $sudo_binary && -f $visudo_binary ]] || {
  echo 'build Linux sudo and visudo with integration/build.sh first' >&2
  exit 2
}
if ! docker image inspect "$image" >/dev/null 2>&1; then
  docker build --platform "linux/$arch" --build-arg "BASE=${SUDO_IT_BASE:-ubuntu:26.04}" \
    -t "$image" "$here" >"$out/conformance/image-build.log" 2>&1
fi
cid=$(docker create --init --platform "linux/$arch" --hostname sudo-it --network none \
  --cap-add SYS_PTRACE --cap-add SYS_ADMIN -v "$out:/out" \
  -e HOST_UID="$(id -u)" -e HOST_GID="$(id -g)" \
  --entrypoint /usr/bin/python3 "$image" /opt/conformance/run.py "$@")
trap 'docker rm -f "$cid" >/dev/null 2>&1 || true' EXIT
docker cp -q "$sudo_binary" "$cid:/opt/impl/sudo"
docker cp -q "$visudo_binary" "$cid:/opt/impl/visudo"
docker cp -q "$here/conformance" "$cid:/opt/conformance"
set +e
docker start -a "$cid" 2>&1 | tee "$out/conformance/run.log"
status=${PIPESTATUS[0]}
set -e
exit "$status"
