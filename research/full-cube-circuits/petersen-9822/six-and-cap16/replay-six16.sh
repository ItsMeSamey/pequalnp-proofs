#!/bin/sh
set -eu
cd "$(dirname "$0")"
src=$PWD
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
cd "$tmp"
for f in profile6 canon6; do c++ -std=c++20 -O3 "$src/$f.cpp" -o "$f"; done
if [ -f "$src/six-all.txt.gz" ]; then gzip -dc "$src/six-all.txt.gz" > six-all.txt
else ./profile6 10 4 | ./canon6 > six-all.txt; fi
for f in six16 six16-fast; do c++ -std=c++20 -O3 "$src/$f.cpp" -o "$f"; ./"$f"; done
./six16 3 0 41719 check > d3
./six16-fast 4 0 41719 check > d4
cmp d3 "$src/size16-d3.ac"
cmp d4 "$src/size16-d4.ac"
