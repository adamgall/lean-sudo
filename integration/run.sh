#!/usr/bin/env bash

















set -euo pipefail

here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
usage() { echo "usage: $0 [--visudo] reference|sudo-rs|--build|<path-to-binary> [test-name-filter]" >&2; exit 2; }
visudo=0
if [[ ${1:-} == --visudo ]]; then visudo=1; shift; fi
[[ $# -ge 1 && $# -le 2 ]] || usage
impl=$1
filter=${2:-}
image=${SUDO_IT_IMAGE:-lean-sudo-it}
if [[ $impl == --build ]]; then
  "$here/build.sh" >/dev/null
  impl="$(dirname "$here")/.lake/linux/sudo"
  [[ $visudo == 1 ]] && impl="$(dirname "$here")/.lake/linux/visudo"
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

mkdir -p "$here/out"
buildlog="$here/out/build.log"
build() {
  docker build --build-arg "BASE=$1" -t "$image" "$here" >"$buildlog" 2>&1
}
if [[ -n ${SUDO_IT_BASE:-} ]]; then
  build "$SUDO_IT_BASE" || { cat "$buildlog" >&2; exit 2; }
elif ! build ubuntu:26.04; then
  echo "# ubuntu:26.04 build failed; retrying with ubuntu:devel" >&2
  build ubuntu:devel || { cat "$buildlog" >&2; exit 2; }
fi


cid=$(docker create \
  --hostname sudo-it --network none --cap-add SYS_PTRACE --cap-add SYS_ADMIN \
  -v "$here/out:/out" \
  -e IMPL_LABEL="$label" -e HOST_UID="$(id -u)" -e HOST_GID="$(id -g)" \
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
echo "# logs: $here/out/$label.tap, $here/out/$label.log" >&2
exit "$rc"
