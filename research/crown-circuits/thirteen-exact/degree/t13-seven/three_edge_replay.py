from few_groups import check
from pathlib import Path
from tempfile import TemporaryDirectory
from subprocess import run
import hashlib,sys
with TemporaryDirectory(dir=sys.argv[2]) as d:
    for i,data in enumerate([(1,1,5,2,2,6),(3,5,6,1,2,4)]):
        stem=Path(d)/str(i)
        assert check(3,data,0,certificate=stem) is False
        cnf,p=stem.with_suffix('.cnf'),stem.with_suffix('.drat')
        assert b's VERIFIED' in run([sys.argv[1],cnf,p],check=True,capture_output=True).stdout
        print(data,hashlib.sha256(cnf.read_bytes()).hexdigest(),flush=True)
        cnf.unlink();p.unlink()
