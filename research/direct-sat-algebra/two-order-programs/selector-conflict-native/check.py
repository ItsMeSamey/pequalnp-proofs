from conflicts import solve,accepts_cnf
from pathlib import Path
from random import Random
from itertools import product
import sys,json
sys.path.insert(0,str(Path(__file__).resolve().parent.parent/'selector-variable-compiler'))
from compiler import compile_cnf,decode
out=[]
def test(n,cs,label):
    N,physical,sel=compile_cnf(n,cs)
    # Relabel every physical bit, then discard metadata for solving.
    perm=list(range(1,N+1));rng=Random(7700+n);rng.shuffle(perm)
    raw=[tuple(perm[abs(l)-1]*(1 if l>0 else -1) for l in row) for row in physical]
    rng.shuffle(raw);ans=solve(N,raw)
    if ans['status']=='sat':
        x=sum(((ans['witness']>>(j-1))&1)<<i for i,j in enumerate(perm))
        assert accepts_cnf(cs,decode(x,sel))
    print(label,n,N,ans['status'],ans['reason'],ans['cost']['data_probes'])
    out.append(dict(label=label,variables=n,physical=N,**ans));return ans

for n in (3,7,15):
    cs=[]
    for i in range(n-1):
        a,b=i+1,i+2;cs.extend([(a,b),(-a,-b)])
    assert test(n,cs,'path')['status']=='sat'
    cs.extend([(1,n),(-1,-n)])
    assert test(n,cs,'odd cycle')['status']=='unsat'
cs=[tuple(-j if v else j for j,v in zip((1,2,3),vals)) for vals in product((0,1),repeat=3)]
assert test(3,cs,'all eight 3-clauses')['status']=='skip'
open('receipt.json','w').write(json.dumps(out,indent=2)+'\n')
