"""Deduplicate finite mixed restrictions by renaming the four branching vertices."""
from itertools import permutations
from functools import lru_cache
from pathlib import Path
from subprocess import run
from tempfile import TemporaryDirectory
import hashlib,sys,json
from clean_mixed import extend,solve
@lru_cache(maxsize=None)
def canonical(rows,swappable=True):
    # A signature contains (augmented tag, partner bits); retain duplicates.
    n=max(t.bit_length()-6 for t,p in rows);best=None
    for b in permutations(range(4)):
        base=[sum(((x>>j)&1)<<b[j] for j in range(4)) for x in range(16)]
        for swap in ([0,1] if swappable else [0]):
            priv=[0,2,1,3] if swap else range(4)
            for extra in permutations(range(max(0,n))):
                def rename(m):
                    y=base[m&15]|(priv[(m>>4)&3]<<4)
                    return y|sum(1<<(6+v) for j,v in enumerate(extra) if m>>(6+j)&1)
                candidate=tuple(sorted((rename(m),priv[p]) for m,p in rows))
                if best is None or candidate<best:best=candidate
    return best
def bank(rows):
    pins=[t for t in rows if t[0].bit_count()==2 and t[0]<64]
    extra=sorted((t,p) for t,p in rows if t>=64)
    # Extra IDs may be permuted by canonicalization; reconstruct in raw-ID order.
    extra.sort(key=lambda r:r[0]>>6)
    return extend(pins,[(t&63,p) for t,p in extra])
def get_key(r,ext,swappable=True):
    return canonical(tuple(sorted([(t,p) for t,p in r if t.bit_count()==2]+[(t|(1<<(6+j)),p) for j,(t,p) in enumerate(ext)])),swappable)
if __name__=='__main__':
    inputfile,path,drat=sys.argv[1:4]
    dirty=len(sys.argv)>4
    if dirty:from one_clean_mixed import check
    keys=set()
    import gzip
    data=(gzip.open(inputfile,'rt').read() if inputfile.endswith('.gz') else Path(inputfile).read_text())
    for l in data.splitlines():
        r,ext=json.loads(l);keys.add(get_key(r,ext,not dirty))
    print('restrictions',len(keys),flush=True)
    with TemporaryDirectory(dir=path) as root:
        for i,key in enumerate(sorted(keys)):
            tests,loads=bank(key)
            f=Path(root)/str(i)
            if dirty:assert check(False,tests,loads,certificate=f) is False
            else:assert solve(tests,loads,certificate=f) is False
            cnf,proof=f.with_suffix('.cnf'),f.with_suffix('.drat')
            assert b's VERIFIED' in run([drat,cnf,proof],check=True,capture_output=True).stdout
            print(i,hashlib.sha256(cnf.read_bytes()).hexdigest(),flush=True)
            cnf.unlink();proof.unlink()
