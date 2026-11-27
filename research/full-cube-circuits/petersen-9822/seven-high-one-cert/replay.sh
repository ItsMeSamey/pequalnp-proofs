#!/usr/bin/env bash
set -eu
cd "$(dirname "$0")"
python higher_forest.py .
cat c{4,5,6}-w0.tsv > higher-zero-run/at-most-two.tsv
cat c{4,5,6}-w1.tsv > higher-one-run/at-most-two.tsv
for f in lowdirect jointclasses3 jointwidth jointbase; do g++ -O2 -std=c++20 "$f.cpp" -o "$f"; done
run(){
  local dir=$1 solver=$2 q=$3 lo=$4 hi=$5 log=$6
  (cd "$dir"; "../$solver" "$q" "$lo" "$hi" at-most-two.tsv > replay-output; gzip -dc "$log.gz" | cmp - replay-output)
}
run higher-zero-run lowdirect 2 0 328 d2.log
run higher-zero-run jointclasses3 3 0 328 d3.log
run higher-zero-run jointwidth 4 0 328 d4.log
run higher-one-run lowdirect 2 0 8193 d2.log
run higher-one-run jointclasses3 3 0 8193 d3.log
run higher-one-run jointwidth 4 0 1334 d4.log
run higher-one-run jointbase 4 1334 8193 d4b.log
python check.py
