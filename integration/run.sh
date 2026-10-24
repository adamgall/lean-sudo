#!/usr/bin/env bash
# Run the end-to-end sudo suite in a throwaway container.
#
#   integration/run.sh <impl> [test-name-filter]
#
# <impl>:  reference   original sudo.ws (Ubuntu package `sudo`, /usr/bin/sudo.ws)
#          sudo-rs     Ubuntu's sudo-rs (/usr/lib/cargo/bin/sudo)
#          <path>      a sudo binary on the host, e.g. .lake/build/bin/sudo
# filter:  extended regex matched against test names (e.g. 'tty-|env-').
#
# Environment: SUDO_IT_BASE (base image, default ubuntu:26.04, falls back to
# ubuntu:devel), SUDO_IT_IMAGE (image tag, default lean-sudo-it).
# Logs: integration/out/<label>.tap and <label>.log (full per-test transcripts).
set -euo pipefail

here=$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)
usage() { echo "usage: $0 reference|sudo-rs|<path-to-sudo-binary> [test-name-filter]" >&2; exit 2; }
[[ $# -ge 1 && $# -le 2 ]] || usage
impl=$1
filter=${2:-}
image=${SUDO_IT_IMAGE:-lean-sudo-it}

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
  --hostname sudo-it --network none \
  -v "$here/out:/out" \
  -e IMPL_LABEL="$label" -e HOST_UID="$(id -u)" -e HOST_GID="$(id -g)" \
  "$image" "$bin" "$filter")
trap 'docker rm -f "$cid" >/dev/null 2>&1 || true' EXIT

if [[ -n $host_bin ]]; then
  docker cp -q "$host_bin" "$cid:/opt/impl/sudo"
fi

set +e
docker start -a "$cid"
rc=$?
set -e
echo "# logs: $here/out/$label.tap, $here/out/$label.log" >&2
exit "$rc"
