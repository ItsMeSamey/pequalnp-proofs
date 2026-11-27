#!/bin/sh
set -eu
cd "$(dirname "$0")"
src=$PWD
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
cd "$tmp"
for f in fiveprofiles canonicalfive; do c++ -O3 -std=c++20 "$src/$f.cpp" -o "$f"; done
./fiveprofiles | ./canonicalfive > canonfive.out
cmp canonfive.out "$src/canonfive.out"
for f in rawbank loose4; do
 sed 's@/workspace/scratch/crown18264/algebra/reverse/canonfive.out@canonfive.out@g' "$src/$f.cpp" > "$f.cpp"
 c++ -O3 -std=c++20 "$f.cpp" -o "$f"
done
./rawbank 2 0 617 > two
./rawbank 3 0 617 > three
./loose4 4 0 617 > four
cmp two "$src/raw2.log"
cmp three "$src/d3-complete.log"
cmp four "$src/loose4.log"
