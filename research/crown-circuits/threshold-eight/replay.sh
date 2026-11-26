#!/usr/bin/env bash
set -euo pipefail
src=$(cd "$(dirname "$0")" && pwd)
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
for f in profile6 canon6 nine-dense nine-direct exact-grant; do
  c++ -O3 -std=c++20 "$src/$f.cpp" -o "$work/$f"
done
"$work/profile6" 8 3 | "$work/canon6" > "$work/profiles"
"$work/nine-direct" 8 0 1 < "$work/profiles" > "$work/low"
"$work/nine-dense" 8 2 3 < "$work/profiles" > "$work/high"
sort -n -k1,1 "$work/low" "$work/high" > "$work/ledger"
cmp "$src/eight-ledger.txt" "$work/ledger"
python3 "$src/extract-eight.py" "$work/profiles" "$work/ledger" > "$work/positive"
"$work/exact-grant" 8 < "$work/positive" > "$work/dynamic"
python3 "$src/fixedpoint-grant.py" 8 < "$work/positive" > "$work/static"
python3 "$src/verify-eight.py" "$work/profiles" "$work/ledger" "$work/dynamic" "$work/static"
python3 "$src/upper-ladder.py"
