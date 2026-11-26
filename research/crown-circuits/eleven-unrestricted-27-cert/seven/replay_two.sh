#!/bin/sh
set -eu
out=${1:?supply a replay directory}
mkdir -p "$out"
python3 positive_control.py positive-seed.json > "$out/positive-bank.tsv"
cmp positive-bank.tsv "$out/positive-bank.tsv"
g++ -std=c++20 -O3 templates11.cpp -o "$out/templates"
g++ -std=c++20 -O3 full11.cpp -o "$out/full"
g++ -std=c++20 -O3 positive_score.cpp -o "$out/positive"
"$out/templates" 2 "$out/catalog.tsv"
cmp physical-two-catalog.tsv "$out/catalog.tsv"
"$out/positive" <positive-bank.tsv > "$out/positive.txt"
cmp positive-control.out "$out/positive.txt"
for c in 0 1 2 3;do "$out/full" 2 "$out/catalog.tsv" "$c" > "$out/cost-$c.tsv";cmp "cost-$c.tsv" "$out/cost-$c.tsv";done
