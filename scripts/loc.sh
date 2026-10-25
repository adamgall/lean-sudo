#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
existing() {
  git ls-files --cached --others --exclude-standard "$@" | while read -r f; do
    [[ -f $f ]] && printf '%s\n' "$f"
  done
}
lean_files=$(existing 'LeanSudo/*.lean' 'LeanSudo/**/*.lean' LeanSudo.lean Main.lean Visudo.lean)
c_files=$(existing 'c/*')
count() { if [[ -n $1 ]]; then echo "$1" | xargs cat | wc -l; else echo 0; fi; }
lean=$(count "$lean_files")
c=$(count "$c_files")
all=$(printf '%s\n%s\n' "$lean_files" "$c_files")
bytes=$(echo "$all" | xargs cat | tr -d ' \t\n' | wc -c)
long=$(echo "$all" | xargs cat | awk 'length > 100' | wc -l)
branches=$(if [[ -n $c_files ]]; then echo "$c_files" | xargs cat | grep -cE '^\s*(if|for|while|switch|do)\b|\belse\s+if\b' || true; else echo 0; fi)
printf 'lean %d  c %d  total %d  non-ws-bytes %d  lines>100 %d  c-branches %d\n' \
  "$lean" "$c" $((lean + c)) "$bytes" "$long" "$branches"
