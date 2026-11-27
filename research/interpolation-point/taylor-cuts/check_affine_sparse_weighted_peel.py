from random import Random
from itertools import combinations
from math import prod
from affine_sparse_weighted_peel import Factor,reduce_weighted,count_cnf,values,row_basis,dot

def check(n,fs):
    rr=reduce_weighted(n,fs)
    def f(x):return prod(t.value(values(t.scope,x)) for t in fs)
    target=sum(f(x) for x in range(1<<n));actual,w=rr.finish(n)
    assert target==actual
    assert f(w)>0 if actual else w is None
    if rr.scale:
        for z in range(1<<n):
            if all(t.value(values(t.scope,z)) for t in rr.factors):
                assert f(rr.lift(z))>0
    if rr.scale and rr.scope:assert rr.finish(0)==(None,None)
    return rr,actual


if __name__=='__main__':
    rng=Random(74259)
    for _ in range(240):
        n=rng.randrange(6); fs=[]
        for j in range(rng.randrange(7)):
            if fs and rng.randrange(3)==0:P=list(rng.choice(fs).scope)
            else:P=list(row_basis(n,[rng.randrange(1<<n) for _ in range(rng.randrange(5))]))
            rng.shuffle(P)
            default=rng.randrange(4)
            entries={v:rng.randrange(5) for v in range(1<<len(P)) if rng.randrange(2)==0}
            fs.append(Factor(tuple(P),default,entries))
        check(n,fs)
    for _ in range(140):
        n=rng.randrange(1,7)
        cs=[tuple(rng.choice((-1,1))*rng.randint(1,n) for _ in range(rng.randrange(5))) for j in range(rng.randrange(8))]
        rs=[(rng.randrange(1<<n),rng.randrange(2)) for _ in range(rng.randrange(3))]
        total,w,R=count_cnf(n,cs,rs,rank_budget=n)
        def feasible(x):
            return all(any(bool(x>>(abs(l)-1)&1)==(l>0) for l in c) for c in cs) and all(dot(x,a)==b for a,b in rs)
        assert total==sum(feasible(x) for x in range(1<<n))
        if total:
            assert feasible(w)
            for z in range(1<<R.n):
                if all(f.value(values(f.scope,z)) for f in R.factors):assert feasible(R.lift_original(z))
    n=4;B=1<<(n+1);edges=[(0,1),(1,2),(2,3),(0,3)]
    fs=[Factor((1<<i,),1,{1:B**sum(i in e for e in edges)}) for i in range(n)]
    fs += [Factor(((1<<i)|(1<<j),),1,{0:B}) for i,j in edges]
    R,Z=check(n,fs)
    assert len(R.scope)==4 and not R.trace and Z//B**len(edges)%B==7
    # High-rank table with one exceptional full word: no enumeration allowed.
    r=95; R=reduce_weighted(r,[Factor(tuple(1<<i for i in range(r)),6,{0:0})])
    total,w=R.finish()
    assert total==6*((1<<r)-1) and w
    print('240 sparse weighted mixtures, 140 pinned CNFs, independent-set residual and rank-95 private scope passed')
