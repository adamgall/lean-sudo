#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
budget=scripts/c-budget.tsv
status=0
branches() { grep -cE '^\s*(if|for|while|switch|do)\b|\belse\s+if\b' "$1" || true; }
for file in c/*; do
  lines=$(wc -l <"$file" | tr -d ' ')
  count=$(branches "$file")
  entry=$(awk -F'\t' -v f="$file" '$1 == f { print $2 "\t" $3 }' "$budget")
  if [[ -z $entry ]]; then
    echo "check-c-boundary: $file has no entry in $budget" >&2
    status=1
    continue
  fi
  max_lines=${entry%%$'\t'*}
  max_branches=${entry##*$'\t'}
  if ((lines > max_lines || count > max_branches)); then
    echo "check-c-boundary: $file has $lines lines/$count branches;" \
      "budget is $max_lines/$max_branches" >&2
    status=1
  fi
done
while IFS=$'\t' read -r file _ _; do
  [[ -e $file ]] || { echo "check-c-boundary: stale budget entry $file" >&2; status=1; }
done <"$budget"
forbid() {
  local pattern=$1 allowed=$2 hits
  hits=$(grep -nE "$pattern" c/* | grep -vE "^($allowed):" || true)
  if [[ -n $hits ]]; then
    echo "check-c-boundary: '$pattern' outside $allowed:" >&2
    echo "$hits" >&2
    status=1
  fi
}
forbid '\b(_Fork|fork|vfork|clone|clone3)\b' 'c/prim_exec.c'
forbid '\bsigaction\s*\(|\bsignal\s*\(' 'c/prim_exec.c|c/prim_timestamp.c'
forbid '\bpthread_create\b|\bsystem\s*\(|\bpopen\s*\(' 'none'
if ((status == 0)); then
  total=$(cat c/* | wc -l | tr -d ' ')
  echo "check-c-boundary: $(ls c | wc -l | tr -d ' ') files, $total lines within budget"
fi
exit "$status"
