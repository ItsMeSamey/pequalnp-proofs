#!/bin/sh
set -eu
out=${1:?provide a writable absolute output directory}
mkdir -p "$out"
g++ -O3 -std=c++20 low-dirty/general11.cpp -o "$out/clean"
g++ -O3 -std=c++20 low-dirty/seven26.cpp -o "$out/one"
for w in 4 5 6 7; do
    "$out/clean" 7 "$w" 0 17 > "$out/clean-$w.txt"
    cmp "low-dirty/clean-seven-$w.log" "$out/clean-$w.txt"
done
for index in 0 1 2 3 4 5; do
    "$out/one" "$index" "$((index+1))" 128 4 5 <low-dirty/one7.txt >"$out/one-$index.txt"
    cmp "low-dirty/one-dirty-$index.log" "$out/one-$index.txt"
done
