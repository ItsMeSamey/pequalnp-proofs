#!/bin/sh
set -eu
out=${1:?specify output directory}
mkdir -p "$out"
g++ -std=c++20 -O3 -march=native hot_anchor.cpp -o "$out/hot"
for t in 1 2 3 4; do
  for r in $(seq 2 $((6-t))); do
    for b in $(seq 0 "$t"); do
      "$out/hot" "$t" "$b" "$r" 5 "$out/positive-$t-$b-$r"
    done
  done > "$out/width-$t.tsv"
  awk -v t="$t" '{p+=$6;h+=$7}END{print t,NR,p,h; if(h)exit 1}' "$out/width-$t.tsv"
done
