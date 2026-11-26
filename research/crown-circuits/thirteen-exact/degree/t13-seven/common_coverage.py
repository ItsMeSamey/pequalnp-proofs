"""Rebuild the complete common-partner incidence and support coverage."""
from pathlib import Path
from tempfile import TemporaryDirectory
from subprocess import run,DEVNULL
import json, sys
from p7_replay import build
from mixed_partner_budget import jobs,extend
here=Path(__file__).resolve().parent
with TemporaryDirectory(dir=sys.argv[1]) as name:
    tmp=Path(name)
    graph=build('quartet_models',tmp); supports=build('p6_debit',tmp); probe=build('probe_envelope',tmp)
    with (tmp/'qmodels.in').open('wb') as f:run([graph,'7','6'],stderr=f,stdout=DEVNULL,check=True)
    for script in ['p6_small.py','probe_profiles.py']:run([sys.executable,here/script,tmp],check=True,stdout=DEVNULL)
    for d in [1,2]:
        prefix=tmp/f'p6-2{d}1'
        with prefix.with_suffix('.in').open('rb') as f,prefix.with_suffix('.masks').open('wb') as out:
            run([supports,'2',str(d),'1','emit'],stdin=f,stderr=out,stdout=DEVNULL,check=True)
        with prefix.with_suffix('.graphs').open('rb') as f,prefix.with_suffix('.live').open('wb') as out:
            run([probe,prefix.with_suffix('.masks'),'1','emit'],stdin=f,stderr=out,stdout=DEVNULL,check=True)
    data=jobs(tmp);assert all((1,3) in r for _,r in data)
    cert=json.loads((here/'common-profiles.json').read_text())
    assert set(extend(r,[(1,3)]) for _,r in data)==set((tuple(map(tuple,ts)),tuple(ls)) for ts,ls in cert)
    print(len(data),'common-partner rows,',len(cert),'distinct mixed-raw restrictions',flush=True)
