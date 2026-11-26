from few_groups import check
from pathlib import Path
from tempfile import TemporaryDirectory
from subprocess import run
import hashlib,sys
tags=(1,1,1,2,2,2,4,4,4)
with TemporaryDirectory(dir=sys.argv[2]) as d:
    for k in map(int,sys.argv[3:]):
        stem=Path(d)/str(k)
        assert check(3,tags,0,certificate=stem,starcuts='full',ordinary_position=k) is False
        cnf,p=stem.with_suffix('.cnf'),stem.with_suffix('.drat')
        assert b's VERIFIED' in run([sys.argv[1],cnf,p],check=True,capture_output=True).stdout
        print(k,hashlib.sha256(cnf.read_bytes()).hexdigest(),flush=True)
        cnf.unlink();p.unlink()
