from itertools import combinations,product
from random import Random
from two_sat_generator_interaction import solve,red_sets
from bijunctive_xor_hull import solve as peel

def check(n,cs,rs):
    def good(x):
        return all(any(bool(x>>(abs(l)-1)&1)==(l>0) for l in c) for c in cs) and all((x&m).bit_count()%2==b for m,b in rs)
    x,stats=solve(n,cs,rs)
    assert (x is not None)==any(good(w) for w in range(1<<n))
    if x is not None:assert good(x)
    return stats

if __name__=='__main__':
    cases=0
    base=[(a,b) for a in (1,-1) for b in (2,-2)]+[(i,) for i in (1,-1,2,-2)]
    for mask in range(256):
        for a,b in product(range(2),repeat=2):
            check(2,[c for i,c in enumerate(base) if mask>>i&1],[(1,a),(2,b)])
            cases+=1
    rng=Random(2291)
    for _ in range(220):
        n=rng.randint(1,7)
        gen=lambda:rng.choice((-1,1))*rng.randint(1,n)
        check(n,[(gen(),gen()) for _ in range(rng.randrange(11))],
              [(rng.randrange(1<<n),rng.randrange(2)) for _ in range(rng.randrange(4))])
        cases+=1
    n=15; cs=[(-j,-j-1) for j in range(1,n)]
    for v in (1,2):
        labels=[0]*n;labels[0]=1;labels[v]=2
        assert peel(n,cs,labels,3)[0]=='UNKNOWN'
        x,stats=solve(n,cs,[(1,1),(1<<v,1)])
        assert (x is not None)==(v==2) and stats['max_degree']==2
    colors=list(red_sets(9,2,5))
    for special in combinations(range(9),5):
        s=sum(1<<i for i in special)
        for red in combinations(special,2):
            mask=sum(1<<i for i in red)
            assert any(c&s==mask for c in colors)
    print(cases,'brute comparisons; two connected peeling-stalled paths; all 1260 isolation patterns passed')
