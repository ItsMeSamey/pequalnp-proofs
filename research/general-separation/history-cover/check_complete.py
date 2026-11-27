from complete import solve,from_cnf
from random import Random
from collections import Counter
rng=Random(1685)
routes=Counter()
for case in range(300):
    n=rng.randrange(1,7)
    clauses=[[rng.choice([-1,1])*rng.randrange(1,n+1) for _ in range(rng.randrange(4))]
             for _ in range(rng.randrange(9))]
    def ok(x):
        return all(any(bool(x>>(abs(l)-1)&1)==(l>0) for l in c) for c in clauses)
    expected=any(ok(x) for x in range(1<<n))
    g,out=from_cnf(n,clauses)
    for t,r in [(16,2),(0,4),(0,0)]:
        w,how=solve(n,g,out,terms=t,rank=r)
        assert (w is not None)==expected and (w is None or ok(w))
        routes[how]+=1
print(dict(routes))
