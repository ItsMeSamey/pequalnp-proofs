#!/usr/bin/env bash
set -eu
src=$(cd "$(dirname "$0")" && pwd)
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
cd "$tmp"
for f in profile6 canon6 check64 dense64; do c++ -O3 -std=c++20 "$src/$f.cpp" -o "$f"; done
./profile6 11 4 | ./canon6 >canon.txt
./check64 11 0 1 <canon.txt >low.txt
head -n 41564 canon.txt | ./dense64 11 2 4 >high.txt
cat low.txt high.txt | sort -nk1 >ledger.txt
cmp "$src/eleven-nonordinary-census.txt" ledger.txt
awk '{banks += $4; if ($1!=NR-1 || $5!=0) exit 1} END {if (NR!=41564 || banks!=105209281) exit 1; print NR,"profiles,",banks,"banks"}' ledger.txt
c++ -O3 -std=c++20 "$src/general11.cpp" -o anchor
for width in 4 5 6; do
  ./anchor 6 "$width" 0 16 >anchor.log 2>&1
  cmp "$src/general-6-$width.log" anchor.log
done
