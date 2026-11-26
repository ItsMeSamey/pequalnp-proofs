"""Check physical row mappings, regenerate their CNFs, and check frozen DRATs."""
import json
import os
from collections import Counter
from pathlib import Path
import subprocess
import sys
from unittest.mock import patch

from clean2 import params

root = Path(__file__).resolve().parent
mapped = [json.loads(x) for x in (root / "two-clean-drat.jsonl").read_text().splitlines()]
expected = {tuple(map(int,l[2:].split("|")[0].split())) for l in (root/"clean2.log").read_text().splitlines() if l.startswith("X ")}
assert len(mapped)==62 and {tuple(r) for r,_,_,_ in mapped}==expected
cases={}
for row,tags,perm,stem in mapped:
    assert sorted(perm)==list(range(4)) and row[2].bit_count()==2
    def relabel(v):
        return sum((v>>src&1)<<j for j,src in enumerate(perm))
    assert relabel(row[2])==12
    assert not (Counter(tags)-Counter(map(relabel,sum(params(row),[]))))
    assert stem==str(Path(stem).parent / ("2_"+"_".join(map(str,tags))))
    assert tuple(tags)==cases.setdefault(stem,tuple(tags))
assert len(cases)==25
if "--mapping-only" in sys.argv:
    print("62 physical rows select 25 CNFs")
    sys.exit()
import certify_sat
for stem,tags in sorted(cases.items()):
    base=root/stem
    cnf=base.with_suffix(".cnf")
    def capture(*,bootstrap_with,with_proof):
        text=cnf.read_text().splitlines()
        clauses=[[int(x) for x in l.split()[:-1]] for l in text[1:]]
        assert all(l.split()[-1]=="0" for l in text[1:])
        assert clauses==bootstrap_with and int(text[0].split()[3])==len(clauses)
        assert max(abs(x) for c in clauses for x in c)<=int(text[0].split()[2])
        raise Captured()
    class Captured(Exception):
        pass
    with patch.object(certify_sat,"Cadical195",capture):
        try:
            certify_sat.certify(tags,2,base)
        except Captured:
            pass
        else:
            raise AssertionError("encoder did not emit a CNF")
    proof=base.with_suffix(".drat")
    msg=subprocess.check_output([os.environ.get("DRAT_TRIM","drat-trim"),str(cnf),str(proof)])
    assert b"s VERIFIED" in msg
print("Verified 62 restricted rows using 25 regenerated CNFs and frozen DRATs")
