#!/usr/bin/env bash
set -euo pipefail
src=$(cd "$(dirname "$0")" && pwd)
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
for f in profile6 canon6 nine-dense nine-direct; do
  c++ -O3 -std=c++20 "$src/$f.cpp" -o "$work/$f"
done
"$work/profile6" 9 3 | "$work/canon6" > "$work/profiles"
"$work/nine-direct" 9 0 1 < "$work/profiles" > "$work/low"
"$work/nine-dense" 9 2 3 < "$work/profiles" > "$work/high"
sort -n -k1,1 "$work/low" "$work/high" > "$work/ledger"
cmp "$src/nine-ledger.txt" "$work/ledger"
python3 "$src/verify-nine-chronology.py" "$work/profiles" "$work/ledger"
python3 "$src/nine-upper.py"
