from pathlib import Path
from tempfile import TemporaryDirectory
from subprocess import run
import hashlib,json,sys
from mixed_partner_budget import check
profiles=json.loads(Path(__file__).with_name('common-profiles.json').read_text())
assert len(profiles)==5
with TemporaryDirectory(dir=sys.argv[2]) as d:
    for i,(tests,loads) in enumerate(profiles):
        base=Path(d)/str(i)
        assert check(1,tests,loads,certificate=base) is False
        cnf=base.with_suffix('.cnf');proof=base.with_suffix('.drat')
        raw=run([sys.argv[1],cnf,proof],capture_output=True,check=True).stdout
        assert b's VERIFIED' in raw
        print(i,hashlib.sha256(cnf.read_bytes()).hexdigest(),'verified',flush=True)
        cnf.unlink();proof.unlink()
