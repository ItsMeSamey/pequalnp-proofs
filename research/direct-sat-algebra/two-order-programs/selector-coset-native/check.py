from itertools import combinations,product
from pathlib import Path
from random import Random
import sys
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'selector-prefix-antichain'))
from prefix import solve
from coset import *

def sig(points,sites):
    return {scope:sum(1<<k for k in {sum(((x>>(a-1))&1)<<j for j,a in enumerate(scope)) for x in points})
            for r in range(3) for scope in combinations(sites,r)}

def models(clauses,x):
    return all(any(bool(x>>(abs(l)-1)&1)==(l>0) for l in c) for c in clauses)

def family(m):
    s=list(range(1,m+1));w=m+1
    x=[m+2+i for i in range(m)];z=[2*m+2+i for i in range(m)]
    cs=[]
    for i in range(m):
        cs.extend([(-s[i],x[i]),(s[i],-x[i]),(s[i],3*m+2+i,4*m+2+i)])
        for a,b,c in product((0,1),repeat=3):
            if a^b^c:cs.append(tuple(-t if bit else t for t,bit in zip((w,x[i],z[i]),(a,b,c))))
    return 5*m+1,cs

if __name__=='__main__':
    r=Random(292)
    for _ in range(120):
        n=4; sites=(1,2,3)
        tail=[tuple(r.choice((-1,1))*r.randint(1,n) for k in range(r.randint(1,3))) for j in range(4)]
        basis=kernel(n,tail_equations(tail)); sets=[]
        for j in range(2):
            cs=[tuple(r.choice((-1,1))*r.choice(sites) for k in range(2)) for t in range(4)]
            sets.append({x for x in range(8) if models(cs,x)})
        L,R=sets; shift=translator(sig(L,sites),sig(R,sites),basis)
        shifts={0}
        for b in basis:shifts|={x^b for x in shifts}
        good={t for t in shifts if {x^(t&7) for x in L}==R}
        assert (shift is None and not good) or shift in good
        assert all(models(tail,x)==models(tail,x^t) for t in shifts for x in range(16))
    for m in (3,5):
        n,cs=family(m);opts={'dominance':False,'state_cap':100}
        raw=solve(n,cs,**opts);orb=TailOrbits(n);red=solve(n,cs,orbit=orb,**opts)
        assert raw['cost']['highwater']==1<<m and red['cost']['highwater']==1
        assert models(cs,red['witness'])
        print(m,raw['cost']['highwater'],red['cost']['highwater'])
