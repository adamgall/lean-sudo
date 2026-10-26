#!/usr/bin/env bash
set -euo pipefail
fingerprint=$(sha256sum integration/coverage/compiler.py integration/coverage/flush.c \
  integration/coverage/asan-options.c | sha256sum)
if [[ ! -f .lake/variant-flags ]] || [[ $(cat .lake/variant-flags) != "$fingerprint" ]]; then
  rm -rf .lake/build
  printf '%s\n' "$fingerprint" > .lake/variant-flags
fi
case "$VARIANT" in
  sanitize) ;;
  asan)
    /usr/bin/clang -c integration/coverage/asan-options.c -o integration/coverage/asan-options.o
    ;;
  coverage)
    /usr/bin/gcc -D_GNU_SOURCE -c integration/coverage/flush.c -o integration/coverage/flush.o
    ;;
  *) exit 2 ;;
esac
lake build sudo visudo
scripts/check-ffi.sh
scripts/check-c-boundary.sh
mkdir -p /out
cp .lake/build/bin/sudo .lake/build/bin/visudo /out/
if [[ $VARIANT == coverage ]]; then
  mkdir -p /out/notes
  find .lake/build -type f \( -name '*.gcno' -o -name '*.c' \) \
    -exec cp --parents '{}' /out/notes/ \;
  cp -a c LeanSudo /out/notes/
fi
printf '%s\n' "$VARIANT" > /out/variant
