#!/usr/bin/env bash
set -euo pipefail
printf 'FROM %s\n' "$FIXTURE_IMAGE" >sudo-test/src/theirs.linux.Dockerfile
cp /suite/pin "/out/$IMPLEMENTATION.pin"
docker image inspect "$FIXTURE_IMAGE" >"/out/$IMPLEMENTATION.image.json"
docker run --rm --network none "$FIXTURE_IMAGE" sh -c \
  'set -e; touch /etc/sudoers; chmod 0440 /etc/sudoers; dpkg-query -W sudo
   sha256sum /usr/bin/sudo /usr/sbin/visudo; sudo -V' \
  >"/out/$IMPLEMENTATION.version.txt" 2>&1
python3 /opt/external/cases.py
