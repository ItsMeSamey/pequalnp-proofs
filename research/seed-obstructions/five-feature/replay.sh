#!/bin/sh
set -eu
cd "$(dirname "$0")"
g++ -std=c++17 -O3 seq.cpp -o seq
g++ -std=c++17 -O3 reachn.cpp -o reachn
g++ -std=c++17 -O3 strong.cpp -o strong
./seq > seq-triples
for n in 1 2 3 4 5; do ./reachn "$n" >"reach.$n"; done
python seqcheck.py
python expand.py
python marker.py
./strong <seq-patterns >seq-unresolved
test ! -s seq-unresolved
