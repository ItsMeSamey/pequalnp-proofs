"""Rebuild every graph and run the C++20 finite obstruction in a temporary directory."""
from hashlib import sha256
from pathlib import Path
from tempfile import TemporaryDirectory
import os
import shutil
import subprocess as sp
import sys
root=Path(__file__).resolve().parent
with TemporaryDirectory() as tmp:
    out=Path(tmp)
    for p in root.glob('*.py'):
        if p.name!='replay.py':shutil.copy(p,out/p.name)
    cxx=os.environ.get('CXX','g++')
    for stem in ['quartet_models','tokens']:
        sp.run([cxx,'-std=c++20','-O3','-march=native',str(root/(stem+'.cpp')),'-o',str(out/stem)],check=True)
    with (out/'models.tsv').open('w') as err:sp.run([out/'quartet_models','7','6'],cwd=out,stdout=sp.DEVNULL,stderr=err,check=True)
    for s in ['graph_types','maximize','sharpen','allrows']:
        sp.run([sys.executable,s+'.py'],cwd=out,check=True)
    with (out/'allrows.tsv').open() as inp,(out/'allrows.log').open('w') as log:
        sp.run([out/'tokens','1000000'],cwd=out,stdin=inp,stdout=log,check=True)
    ledger=(out/'allrows.log').read_bytes();rows=[list(map(int,l.split())) for l in ledger.splitlines()]
    assert len(rows)==119 and [r[0] for r in rows]==list(range(119)) and all(r[2]==0 for r in rows)
    exact=(root/'allrows.log').read_bytes()
    assert ledger==exact
    print('All 119 checked problems are negative. Nodes:',sum(r[3] for r in rows))
    print('Ledger SHA256:',sha256(ledger).hexdigest())
