#!/usr/bin/env bash
set -eu
cd "$(dirname "$0")"
python upper.py
python check.py
python lowconditional.py
cat full6.tsv full5.tsv > at-most-two.tsv
python helper_orbits.py > full6.orbits
for src in directfirst lowdirect joint jointcausal jointthree jointdouble; do
 g++ -O2 -std=c++20 "$src.cpp" -o "$src"
 "./$src" >/dev/null
done
./lowdirect 2 0 226 at-most-two.tsv > replay-d2.log
./directfirst 3 0 6 at-most-two.tsv 0 full6.orbits > replay-d3one.log
./joint 4 0 6 > replay-d4one.log
./jointcausal 4 2 3 > replay-d4causal.log
./directfirst 3 6 12 at-most-two.tsv 0 double-first.orbits > replay-d3two-a.log
./jointthree 3 12 226 > replay-d3two-b.log
./jointdouble 4 6 226 > replay-d4two.log
cmp replay-d2.log d2.log
cmp replay-d4one.log d4joint.log
cmp replay-d4causal.log d4causal.log
cmp replay-d3two-a.log d3-double-first.log
cmp replay-d3two-b.log d3double-b.log
cat d4double-a.log d4double-b.log | cmp - replay-d4two.log
python - <<'PY'
from pathlib import Path
rows=[s.split() for s in Path('replay-d3one.log').read_text().splitlines() if ' atoms ' in s]
assert [int(r[0]) for r in rows]==list(range(6))
assert all(r[-2:]==['hits','0'] for r in rows)
PY
