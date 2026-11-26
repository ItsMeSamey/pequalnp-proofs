"""Rebuild the full six-group four-branching census and check the witness restrictions."""
from collections import Counter
from itertools import product
from pathlib import Path
from tempfile import TemporaryDirectory
from subprocess import run,DEVNULL
import gzip,json,sys
from p7_replay import build
from mixed_partner_budget import extend
here=Path(__file__).resolve().parent
def generate(d):
    graph=build('quartet_models',d);supports=build('p6_debit',d);probe=build('probe_envelope',d)
    with (d/'qmodels.in').open('wb') as f:run([graph,'7','6'],stderr=f,stdout=DEVNULL,check=True)
    for script in ['p6_small.py','probe_profiles.py']:run([sys.executable,here/script,d],check=True,stdout=DEVNULL)
    data={}
    for dirty,shared in [(0,0),(1,0),(1,1),(2,0),(2,1)]:
        prefix=d/f'p6-2{dirty}{shared}'
        with prefix.with_suffix('.in').open('rb') as f,prefix.with_suffix('.masks').open('wb') as out:
            run([supports,'2',str(dirty),str(shared),'emit'],stdin=f,stderr=out,stdout=DEVNULL,check=True)
        with prefix.with_suffix('.graphs').open('rb') as f,prefix.with_suffix('.live').open('wb') as out:
            run([probe,prefix.with_suffix('.masks'),str(shared),'emit'],stdin=f,stderr=out,stdout=DEVNULL,check=True)
        rows=set()
        for line in prefix.with_suffix('.live').read_text().splitlines():
            _,p,q,*tags=map(int,line.split())
            if shared:q=p
            rows.add(tuple(sorted((tag,(p>>k&1)|((q>>k&1)<<1)) for k,tag in enumerate(tags))))
        data[dirty,shared]=rows
    return data
def coverage(data):
    expected={(0,0):1199,(1,0):402,(1,1):7,(2,0):24,(2,1):0}
    assert {k:len(v) for k,v in data.items()}==expected
    for dirty,name in [(0,'clean'),(1,'one-clean')]:
        rows=set()
        with gzip.open(here/(name+'-restrictions.jsonl.gz'),'rt') as f:
            for l in f:
                r,e=json.loads(l);r=tuple(map(tuple,r));e=tuple(map(tuple,e))
                assert not (Counter(e)-Counter(r)) and all(t.bit_count()<2 for t,v in e)
                rows.add(r)
        assert rows==data[dirty,0]
    for shape,ext,fname in [((1,1),[(1,3)],'common-profiles'),((2,0),[],'two-dirty-partners')]:
        assert all(not (Counter(ext)-Counter(r)) for r in data[shape])
        bank={extend(r,ext) for r in data[shape]}
        expected=json.loads((here/(fname+'.json')).read_text())
        assert bank==set((tuple(map(tuple,ts)),tuple(ls)) for ts,ls in expected)
    print('1199 + 402 + 7 + 24 + 0 support layouts covered',flush=True)
if __name__=='__main__':
    with TemporaryDirectory(dir=sys.argv[1]) as tmp:coverage(generate(Path(tmp)))
