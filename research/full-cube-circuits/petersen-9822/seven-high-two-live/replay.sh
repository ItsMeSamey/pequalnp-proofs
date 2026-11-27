#!/usr/bin/env bash
set -eu
cd "$(dirname "$0")"
python pair-parity.py
for x in lowdirect jointclasses3 jointdomains jointquick jointfixed jointpair; do g++ -O2 -std=c++20 "$x.cpp" -o "$x"; done
for pair in 'c5 2' 'c6 1'; do
 read -r c p <<<"$pair"; mkdir -p "$c"; test -f "$c/at-most-two.tsv" || python higher_two.py "$p" "$c/at-most-two.tsv"
done
while read -r c label lo hi src; do
 (cd "$c"; "../$src" "${label:1:1}" "$lo" "$hi" at-most-two.tsv > replay-log; gzip -dc "../$c-$label.log.gz" | cmp - replay-log)
done < completed-stages.tsv
python check.py
