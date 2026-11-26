"""Independent SAT replay of the final direct-receiver compatibility filter."""
from functools import lru_cache
from itertools import combinations
from pathlib import Path
from pysat.solvers import Glucose4
from sys import argv
from collections import Counter
L=[sum(1<<(2*j+(p>>j&1)) for j in range(4)) for p in range(16)]
env=[sum((1<<i) for i,a in enumerate(L) if a&e) for e in range(256)]
base=[1<<j for j in range(9)]
def expressions(S,hs):
    candidates=set()
    for h in hs:
        for b in base+list(hs):
            if h==b:continue
            f=b|h
            if f&256 or env[f&255]==65535:
                e=f&255
                if (S&~env[e]).bit_count()<=1:candidates.add(e)
    return tuple(sorted(candidates))
@lru_cache(None)
def check(S,ee):
    points=[p for p in range(16) if S>>p&1];rules=[];nv=44
    for i,p in enumerate(points):
        choices=[]
        for e in ee:
            bits=[[1+4*q+j for j in range(4) if e>>(2*j+(v>>j&1))&1] for q,v in enumerate(points)]
            if any(not ls and q!=i for q,ls in enumerate(bits)):continue
            nv+=1;choices.append(nv)
            for q,ls in enumerate(bits):
                if q==i:
                    for b in ls:rules.append([-nv,-b])
                else:rules.append([-nv]+ls)
        rules.append(choices)
    with Glucose4(bootstrap_with=rules) as s:return s.solve()
if __name__=='__main__':
    f=Path('coverfamilies.out')
    groups={}
    for row in f.read_text().splitlines():
        S,*hs=map(int,row.split());key=S,expressions(S,hs);groups[key]=groups.get(key,0)+1
    print('survivor families',sum(groups.values()),'distinct expression systems',len(groups),flush=True)
    lo=int(argv[1]) if len(argv)>1 else 0;N=int(argv[2]) if len(argv)>2 else 1
    solved=0
    for j,key in enumerate(sorted(groups)):
        if j%N!=lo:continue
        assert not check(*key),key
        solved+=1
        if solved%2000==0:print('checked',solved,flush=True)
    print('Glucose UNSAT',solved,flush=True)
