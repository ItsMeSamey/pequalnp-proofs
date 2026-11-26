#!/bin/sh
set -eu
dirty=${1:?supply a dirty count from 3 to 6}
out=${2:?supply an output directory}
case "$dirty" in 3|4|5|6) ;; *) exit 2 ;; esac
mkdir -p "$out"
for tool in templates11 project11 cycles11 two_tags11 residual11 positive_anchor_score; do
    g++ -std=c++20 -O3 "$tool.cpp" -o "$out/$tool"
done
"$out/positive_anchor_score" <positive-bank.tsv >"$out/positive-anchor.out"
cmp positive-anchor.out "$out/positive-anchor.out"
"$out/templates11" "$dirty" "$out/catalog.tsv"
"$out/project11" "$dirty" "$out/catalog.tsv" >"$out/projection.tsv"
awk 'NR==FNR { if ($5) kept[$1]=1; next } $1 in kept' "$out/projection.tsv" "$out/catalog.tsv" >"$out/eligible.tsv"
"$out/cycles11" "$dirty" "$out/eligible.tsv" >"$out/cycles.tsv"
"$out/two_tags11" "$dirty" "$out/eligible.tsv" >"$out/tags.tsv"
for cost in 0 1 2; do
    "$out/residual11" "$dirty" "$out/eligible.tsv" "$cost" >"$out/full-$cost.tsv"
done
python3 verify_higher.py "$dirty" "$out/catalog.tsv" "$out/cycles.tsv" "$out/tags.tsv" "$out/full-0.tsv" "$out/full-1.tsv" "$out/full-2.tsv" --projection "$out/projection.tsv"
