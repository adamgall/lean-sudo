#!/usr/bin/env bash
# Run the end-to-end sudo suite in a throwaway container.
#
#   integration/run.sh <impl> [test-name-filter]
#   integration/run.sh --visudo reference|<path-to-visudo>|--build [test-name-filter]
#
# <impl>:  reference   original sudo.ws (Ubuntu package `sudo`, /usr/bin/sudo.ws)
#          sudo-rs     Ubuntu's sudo-rs (/usr/lib/cargo/bin/sudo)
#          <path>      a sudo binary on the host, e.g. .lake/linux/sudo
#          --build     build lean-sudo's Linux sudo/visudo first (integration/build.sh,
#                      a container build; works on macOS) and test that binary
# filter:  extended regex matched against test names (e.g. 'tty-|env-').
# --visudo runs visudo-tests.sh (copied in) instead of tests.sh, against
#          /usr/sbin/visudo.ws (reference) or a host visudo binary.
#
# Environment: SUDO_IT_BASE (base image, default ubuntu:26.04, falls back to
# ubuntu:devel), SUDO_IT_IMAGE (image tag, default lean-sudo-it).
# Logs: integration/out/<label>.tap and <label>.log (full per-test transcripts).
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

# --- visudo suite hook ------------------------------------------------------
entry=()
if [[ $visudo == 1 ]]; then
  case $impl in
    reference) bin=/usr/sbin/visudo.ws; label=visudo-reference ;;
    sudo-rs)   usage ;;
    *)         bin=/opt/impl/visudo; label=visudo-$(basename "$host_bin")
               [[ $label == visudo-visudo ]] && label=custom-visudo ;;
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

# Only the log directory is mounted (writable); everything else is copied in.
cid=$(docker create \
  --hostname sudo-it --network none --cap-add SYS_PTRACE \
  -v "$here/out:/out" \
  -e IMPL_LABEL="$label" -e HOST_UID="$(id -u)" -e HOST_GID="$(id -g)" \
  "${entry[@]}" "$image" "$bin" "$filter")
trap 'docker rm -f "$cid" >/dev/null 2>&1 || true' EXIT

if [[ -n $host_bin ]]; then
  docker cp -q "$host_bin" "$cid:$bin"
fi
if [[ $visudo == 1 ]]; then
  docker cp -q "$here/visudo-tests.sh" "$cid:/opt/impl/visudo-tests.sh"
fi

set +e
docker start -a "$cid"
rc=$?
set -e
echo "# logs: $here/out/$label.tap, $here/out/$label.log" >&2
exit "$rc"
