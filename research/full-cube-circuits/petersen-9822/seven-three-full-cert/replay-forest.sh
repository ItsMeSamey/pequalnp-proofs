#!/usr/bin/env bash
set -eu
cd "$(dirname "$0")"
python forest3.py
python single_paid.py
python repeat_paid.py
for x in lowdirect jointthree jointdouble; do g++ -O2 -std=c++20 "$x.cpp" -o "$x"; done
for triple in 'forest3-run forests3.tsv 11' 'single-paid-run single-paid.tsv 177' 'repeat-paid-run repeat-paid.tsv 21'; do
 read -r dir key n <<<"$triple"
 (cd "$dir"; ln -sf "../$key" at-most-two.tsv; ../lowdirect 2 0 "$n" at-most-two.tsv > r2; ../jointthree 3 0 "$n" > r3; ../jointdouble 4 0 "$n" > r4; cmp d2.log r2; cmp d3.log r3; cat d4*.log | cmp - r4)
done
python check.py
