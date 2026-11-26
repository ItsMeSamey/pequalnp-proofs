#!/usr/bin/env bash
set -eu
src=$(cd "$(dirname "$0")" && pwd)
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
cd "$tmp"
for f in profile6 canon6 check64 dense64; do c++ -O3 -std=c++20 "$src/$f.cpp" -o "$f"; done
./profile6 10 3 | ./canon6 >canon.txt
./check64 10 0 1 <canon.txt >low.txt
./dense64 10 2 3 <canon.txt >high.txt
cat low.txt high.txt | sort -nk1 >ledger.txt
cmp "$src/ten-six-census.txt" ledger.txt
awk '{banks += $4; if ($1!=NR-1 || $5!=0) exit 1} END {if (NR!=25601 || banks!=4824777) exit 1; print NR,"profiles,",banks,"banks"}' ledger.txt
