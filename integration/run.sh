#!/usr/bin/env bash

















set -euo pipefail

here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
usage() {
  echo "usage: $0 [--arch amd64|arm64] [--visudo] reference|sudo-rs|--build|<binary> [filter]" >&2
  exit 2
}
case $(uname -m) in
  arm64|aarch64) arch=arm64 ;;
  x86_64|amd64) arch=amd64 ;;
  *) usage ;;
esac
visudo=0
while [[ $# -gt 0 ]]; do
  case $1 in
    --arch) [[ $# -ge 2 ]] || usage; arch=$2; shift 2 ;;
    --visudo) visudo=1; shift ;;
    *) break ;;
  esac
done
[[ $arch =~ ^(amd64|arm64)$ ]] || usage
[[ $# -ge 1 && $# -le 2 ]] || usage
impl=$1
filter=${2:-}
image="${SUDO_IT_IMAGE:-lean-sudo-it}-$arch"
if [[ $impl == --build ]]; then
  "$here/build.sh" --arch "$arch" >/dev/null
  impl="$(dirname "$here")/.lake/linux-$arch/sudo"
  [[ $visudo == 1 ]] && impl="$(dirname "$here")/.lake/linux-$arch/visudo"
fi

host_bin=
case $impl in
  reference) bin=/usr/bin/sudo.ws;        label=reference ;;
  sudo-rs)   bin=/usr/lib/cargo/bin/sudo; label=sudo-rs ;;
  -h|--help) usage ;;
  *)
    [[ -f $impl ]] || { echo "$0: $impl: no such file (build it first?)" >&2; exit 2; }
    host_bin=$(readlink -f "$impl")
    bin=/opt/impl/sudo
    label=$(basename "$host_bin")
    [[ $label == sudo ]] && label=custom-sudo
    ;;
esac


entry=()
visudo_env=()
sibling_sudo=
if [[ $visudo == 1 ]]; then
  case $impl in
    reference) bin=/usr/sbin/visudo.ws; label=visudo-reference ;;
    sudo-rs)   usage ;;
    *)         bin=/opt/impl/visudo; label=visudo-$(basename "$host_bin")
               [[ $label == visudo-visudo ]] && label=custom-visudo

               if [[ -f $(dirname "$host_bin")/sudo ]]; then
                 sibling_sudo=$(dirname "$host_bin")/sudo
                 visudo_env=(-e VISUDO_SUDO_BINARY=/opt/impl/sudo)
               fi ;;
  esac
  entry=(--entrypoint /opt/impl/visudo-tests.sh)
fi

impl_label=$label
label="${SUDO_IT_LABEL:-$label-$arch}"
out="${SUDO_IT_OUT:-$here/out}"
mkdir -p "$out"
buildlog="$out/build-$arch-$label.log"
build() {
  docker build --platform "linux/$arch" --build-arg "BASE=$1" \
    -t "$image" "$here" >"$buildlog" 2>&1
}
if [[ -n ${SUDO_IT_BASE:-} ]]; then
  build "$SUDO_IT_BASE" || { cat "$buildlog" >&2; exit 2; }
elif ! build ubuntu:26.04; then
  echo "# ubuntu:26.04 build failed; retrying with ubuntu:devel" >&2
  build ubuntu:devel || { cat "$buildlog" >&2; exit 2; }
fi


cid=$(docker create --platform "linux/$arch" \
  --hostname sudo-it --network none --cap-add SYS_PTRACE --cap-add SYS_ADMIN \
  -v "$out:/out" \
  -e IMPL_LABEL="$impl_label" -e IMPL_OUTPUT_LABEL="$label" \
  -e HOST_UID="$(id -u)" -e HOST_GID="$(id -g)" \
  "${visudo_env[@]}" "${entry[@]}" "$image" "$bin" "$filter")
trap 'docker rm -f "$cid" >/dev/null 2>&1 || true' EXIT

if [[ -n $host_bin ]]; then
  docker cp -q "$host_bin" "$cid:$bin"
fi
if [[ $visudo == 1 ]]; then
  docker cp -q "$here/visudo-tests.sh" "$cid:/opt/impl/visudo-tests.sh"
  [[ -n $sibling_sudo ]] && docker cp -q "$sibling_sudo" "$cid:/opt/impl/sudo"
fi

set +e
docker start -a "$cid"
rc=$?
set -e
echo "# logs: $out/$label.tap, $out/$label.log" >&2
exit "$rc"
