#!/usr/bin/env bash





set -euo pipefail
cd "$(dirname "$0")/.."
files=$(git ls-files 'LeanSudo/*.lean' 'LeanSudo/**/*.lean' LeanSudo.lean Main.lean Visudo.lean 'c/*')
lean=$(git ls-files 'LeanSudo/*.lean' 'LeanSudo/**/*.lean' LeanSudo.lean Main.lean Visudo.lean | xargs cat | wc -l)
c=$(git ls-files 'c/*' | xargs cat | wc -l)
bytes=$(echo "$files" | xargs cat | tr -d ' \t\n' | wc -c)
long=$(echo "$files" | xargs cat | awk 'length > 100' | wc -l)
printf 'lean %d  c %d  total %d  non-ws-bytes %d  lines>100 %d\n' "$lean" "$c" $((lean + c)) "$bytes" "$long"
