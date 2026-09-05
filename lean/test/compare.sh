#!/usr/bin/env bash
# Cross-check Definition 5.1 (lean/Bm4Compute.lean) against yaBMS `bms -v4`.
# Usage: BMS=/path/to/yaBMS/c/bms LEANPROJ=/path/to/mathlib-project ./compare.sh
set -u
here=$(cd "$(dirname "$0")" && pwd)
: "${BMS:?set BMS to the yaBMS c/bms binary}"
: "${LEANPROJ:?set LEANPROJ to a Lean project with Mathlib built}"
work=$(mktemp -d)
{ cat "$here/../Bm4/Compute.lean"; echo
  while IFS='|' read -r inp n out; do echo "#eval BM4C.run \"$inp\" $n"; done < "$here/cases.txt"
} > "$work/cmp.lean"
leanman check --backend lean -m bm4-compare -C "$LEANPROJ" "$work/cmp.lean" > "$work/out" 2>&1
grep '^"' "$work/out" | sed 's/^"//; s/"$//' > "$work/got"
cut -d'|' -f3 "$here/cases.txt" > "$work/exp"
if diff "$work/got" "$work/exp"; then echo "ALL_MATCH ($(wc -l < "$work/exp") cases)"; else echo MISMATCH; exit 1; fi
