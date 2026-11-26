#!/usr/bin/env bash
set -euo pipefail
src=$(cd "$(dirname "$0")" && pwd)
out=$(mktemp -d)
trap 'rm -rf "$out"' EXIT
cd "$out"
for name in saturated anchors anchors_fast library library_straddle; do
  "${CXX:-c++}" -std=c++20 -O3 -mpopcnt "$src/$name.cpp" -o "$name"
done
./saturated 4 >width4.out
./saturated 4 0 403 0 >width4-parity-free.out
./saturated 3 >width3-three-outside.out
./anchors 3 >anchors3.out
./anchors_fast 2 >fast2.out
./anchors_fast 1 >fast1.out
for w in 1 2 3; do
  input="fast$w.out"
  if [[ $w == 3 ]]; then input="anchors3.out"; fi
  ./library <"$input" | sort -n -k1,1 -k2,2 >"library$w.out"
done
./library_straddle <fast1.out | sort -n -k1,1 -k2,2 >library1-straddle.out
for f in *.out; do diff -u "$src/$f" "$f"; done
python "$src/verify.py"
