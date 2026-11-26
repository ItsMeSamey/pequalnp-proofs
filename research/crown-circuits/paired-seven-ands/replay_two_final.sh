#!/bin/sh
set -eu
out=${1:?specify output directory}
mkdir -p "$out"
for src in two_saturated two_anchor two_sym; do g++ -std=c++20 -O3 -march=native "$src.cpp" -o "$out/$src"; done
"$out/two_saturated" 4 0 244 > "$out/width-four.tsv"
"$out/two_anchor" 3 0 244 "$out/witness-three-" > "$out/width-three.tsv"
"$out/two_sym" 2 0 244 "$out/witness-two-" > "$out/width-two.tsv"
"$out/two_sym" 1 0 244 "$out/witness-one-" > "$out/width-one.tsv"
diff -u two-dirty-width-four.tsv "$out/width-four.tsv"
diff -u two-dirty-width-three.tsv "$out/width-three.tsv"
diff -u two-dirty-width-two.tsv "$out/width-two.tsv"
diff -u two-dirty-width-one.tsv "$out/width-one.tsv"
