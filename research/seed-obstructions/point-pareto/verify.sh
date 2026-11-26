#!/usr/bin/env bash
set -euo pipefail
here="$(cd "$(dirname "$0")" && pwd)"
input="$(realpath "${1:-$here/L-meta-18968.json}")"
tmpdir="$(mktemp -d)"
trap 'rm -rf "$tmpdir"' EXIT
python "$here/six_outputs.py" "$input" "$tmpdir/six.txt"
python "$here/nine_leaf_banks.py" "$input" "$tmpdir/six.txt" > "$tmpdir/banks.txt"
cmp "$here/cost-nine-six.txt" "$tmpdir/banks.txt"
python "$here/check.py" "$input" --gates 8 --selected 7 --single-hidden --require-unsat
python "$here/check.py" "$input" --gates 8 --selected 8 --require-unsat
python "$here/check.py" "$input" --width 12 --gates 4 --require-unsat
python "$here/star_recovery.py" "$input"
