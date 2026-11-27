#!/bin/sh
set -eu
BASE=$(CDPATH='' cd -- "$(dirname "$0")" && pwd)
RUN=$(mktemp -d)
trap 'rm -rf "$RUN"' EXIT
cd "$RUN"
gzip -dc "$BASE/six-all.txt.gz" > six-all.txt
# Compare decimal masks as strings, avoiding float conversion in awk.
python3 - <<'PY'
from pathlib import Path
f=str(2**64-1);lines=Path('six-all.txt').read_text().splitlines()
assert len(lines)==41719
rows=[l for l in lines if l.split().count(f)==4];assert len(rows)==96
Path('six-two-conditional.txt').write_text(''.join(l+'\n' for l in rows))
PY
build(){ c++ -O3 -std=c++20 "$BASE/$1.cpp" -o "$1"; }
check(){ gzip -dc "$BASE/logs/$1.gz" | cmp - "$1"; }
for k in sixbank sixac sixac-helper six-fixed-activ six-one-act six-one-early six17-fast six17-twohelpers six17-onehelper six17-onefast six17-allraw six17-seed4 six17-finals six17-joint;do build "$k";done
cp "$BASE/control4-1.txt" .
./six17-joint > joint-control.log
check joint-control.log
python3 "$BASE/forward.py" "$BASE/priced-9-1.json" > forward18.json
python3 - "$BASE/physical-18-1.json" <<'PY'
import json,sys
assert json.load(open('forward18.json'))==json.load(open(sys.argv[1]))
PY
./sixbank 2 0 19 > six-two-d2.log; check six-two-d2.log
./sixac 2 19 96 > six-two-d2b.log; check six-two-d2b.log
./sixac-helper 3 0 96 > six-two-d3.log; check six-two-d3.log
./six-fixed-activ 4 0 96 > six-fixed-d4.log; check six-fixed-d4.log
./six-one-act 4 0 46 > six-one-d4.log; check six-one-d4.log
./six-one-early 4 46 96 > six-one-d4b.log; check six-one-d4b.log
./six17-fast 2 0 41719 check > size17-d2.ac; check size17-d2.ac
./six17-fast 3 0 41718 check > size17-d3.ac; check size17-d3.ac
./six17-twohelpers 4 0 41719 > size17-d4-two.ac; check size17-d4-two.ac
./six17-onehelper 4 0 10576 check > size17-d4-one-complete.ac
./six17-onefast 4 10576 41719 check >> size17-d4-one-complete.ac
check size17-d4-one-complete.ac
./six17-allraw 4 0 41719 > size17-d4-allraw.filter; check size17-d4-allraw.filter
awk '$2=="predecessor-compatible"{print $1}' size17-d4-allraw.filter > size17-allraw-ids.txt
./six17-seed4 4 0 41719 > size17-d4-seeds.ac; check size17-d4-seeds.ac
awk '$1=="packing"{print $2}' size17-d4-seeds.ac > size17-final-six.ids
./six17-finals 4 0 21164 banks check > final5.ac; check final5.ac
./six17-joint 4 21580 41718 > final3.joint; check final3.joint
