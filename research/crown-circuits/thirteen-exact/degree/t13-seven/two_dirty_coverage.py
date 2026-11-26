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
    for d in [2]:
        prefix=tmp/f'p6-2{d}0'
        with prefix.with_suffix('.in').open('rb') as f,prefix.with_suffix('.masks').open('wb') as out:
            run([supports,'2',str(d),'0','emit'],stdin=f,stderr=out,stdout=DEVNULL,check=True)
        with prefix.with_suffix('.graphs').open('rb') as f,prefix.with_suffix('.live').open('wb') as out:
            run([probe,prefix.with_suffix('.masks'),'0','emit'],stdin=f,stderr=out,stdout=DEVNULL,check=True)
    data=jobs(tmp)
    cert=json.loads((here/'two-dirty-partners.json').read_text())
    assert set(extend(r,()) for _,r in data)==set((tuple(map(tuple,ts)),tuple(ls)) for ts,ls in cert)
    print(len(data),'two-dirty distinct-partner layouts,',len(cert),'pure restrictions',flush=True)
