#!/bin/sh
set -eu
out=${1:?specify a replay directory}
mkdir -p "$out"
for x in three_cut three_saturated three_hard three_roots three_helpers three_semantic three_anchor; do
    g++ -std=c++20 -O3 "$x.cpp" -o "$out/$x"
done
python three_catalog.py affordable > "$out/affordable.tsv"
"$out/three_cut" "$out/affordable.tsv" > "$out/cuts.tsv"
cmp "$out/cuts.tsv" three-hard-anchor-cuts.tsv
for w in 3 4; do "$out/three_saturated" "$w" "$out/affordable.tsv" > "$out/saturated-$w.tsv"; done
cmp "$out/saturated-4.tsv" three-dirty-width-four.tsv
cmp "$out/saturated-3.tsv" three-dirty-width-three-residue-three.tsv
python three_catalog.py live "$out/cuts.tsv" > "$out/live.tsv"
"$out/three_hard" "$out/live.tsv" > "$out/hard.tsv"
cmp "$out/hard.tsv" three-hard-hot-filter.tsv
python three_catalog.py filtered "$out" > "$out/filtered.tsv"
cmp "$out/filtered.tsv" three-filtered-catalog.tsv
"$out/three_helpers" "$out/live.tsv" 3 0 40000 > "$out/cost3.tsv"
cmp "$out/cost3.tsv" three-cost-three-complete.tsv
"$out/three_semantic" "$out/live.tsv" 2 0 40000 > "$out/cost2.tsv"
cmp "$out/cost2.tsv" three-cost-two-complete.tsv
"$out/three_roots" "$out/filtered.tsv" "$out/roots.tsv" > "$out/root-counts.tsv"
cmp "$out/root-counts.tsv" three-hard-root-counts.tsv
cmp "$out/roots.tsv" three-hard-roots.tsv
for c in 0 1; do
    case "$c" in 0) word=zero;; 1) word=one;; esac
    while read -r file id rest; do
        case "$file" in
            *-a-*|*-iso-*) "$out/three_anchor" "$out/filtered.tsv" "$out/roots.tsv" "$c" "$id" "$((id+1))" > "$out/current.tsv";;
            *) "$out/three_semantic" "$out/filtered.tsv" "$c" "$id" "$((id+1))" > "$out/current.tsv";;
        esac
        echo "$id $rest" > "$out/expected.tsv"
        cmp "$out/expected.tsv" "$out/current.tsv"
    done < "three-cost-$word-representatives.tsv"
done
python verify_three_strata.py 0 1
