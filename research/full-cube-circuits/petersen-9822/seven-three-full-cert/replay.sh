#!/usr/bin/env bash
set -eu
cd "$(dirname "$0")"
./replay-forest.sh
python two_paid.py
test -f three-paid.tsv || python three_paid.py three-paid.tsv
for src in jointdouble-bounded jointcache jointclasses jointclasses3 jointearly jointwidth; do g++ -O2 -std=c++20 "$src.cpp" -o "$src"; done
for family in two-paid three-paid; do ln -sf "../$family.tsv" "$family-run/at-most-two.tsv"; done
run(){
 local folder=$1 src=$2 q=$3 lo=$4 hi=$5 log=$6
 (cd "$folder"; if [[ "$src" == lowdirect ]]; then "../$src" "$q" "$lo" "$hi" at-most-two.tsv >last-replay; else "../$src" "$q" "$lo" "$hi" >last-replay; fi
 gzip -dc "$log.gz" | cmp - last-replay)
}
run two-paid-run lowdirect 2 0 2082 d2.log
run two-paid-run jointthree 3 0 1860 d3.log
run two-paid-run jointthree 3 1860 2082 d3b.log
run two-paid-run jointdouble-bounded 4 0 230 d4.log
run two-paid-run jointcache 4 230 981 d4b.log
run two-paid-run jointclasses 4 981 2082 d4c.log
run three-paid-run lowdirect 2 0 15201 d2.log
run three-paid-run jointclasses3 3 0 15201 d3.log
run three-paid-run jointearly 4 0 2803 d4.log
run three-paid-run jointearly 4 2803 8847 d4b.log
run three-paid-run jointwidth 4 8847 15201 d4c.log
python check-full.py
