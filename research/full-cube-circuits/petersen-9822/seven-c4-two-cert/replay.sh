#!/usr/bin/env bash
set -eu
cd "$(dirname "$0")"
test -f at-most-two.tsv || python higher_two.py 3 at-most-two.tsv
for s in lowdirect jointclasses3 jointbase jointarc jointdomains; do g++ -O2 -std=c++20 "$s.cpp" -o "$s"; done
run(){
 "./$1" "$2" "$3" "$4" at-most-two.tsv > replay-log
 gzip -dc "receipts/$5.log.gz" | cmp - replay-log
}
run lowdirect 2 0 18024 d2
run jointclasses3 3 0 18024 d3
run jointbase 4 0 4165 d4
run jointbase 4 4165 7958 d4b
run jointarc 4 7958 11714 d4c
run jointdomains 4 11714 16427 d4d
run jointdomains 4 16427 18024 d4e
