from itertools import combinations,product
from random import Random
from labelled_switching_generators import prepare,solve


def matchings(V,es):
    if not V:
        yield ()
        return
    first=min(V)
    for i,(u,v,g) in enumerate(es):
        if first in (u,v) and u in V and v in V:
            for trace in matchings(V-{u,v},es):
                yield (i,)+trace


def hub(b,regauge):
    words=list(product(range(3),repeat=b))
    z=len(words)
    n=z+1
    rng=Random(731)
    q=[tuple(rng.randrange(3) for _ in range(b)) if regauge else (0,)*b for u in range(n)]
    es=[]
    for u,v in combinations(range(n),2):
        g=words[u] if v==z else (0,)*b
        es.append((u,v,tuple((a+c+d)%3 for a,c,d in zip(g,q[u],q[v]))))
    gen=[]
    for k in range(b):
        perm=tuple(words.index(tuple((x+int(j==k))%3 for j,x in enumerate(w))) for w in words)+(z,)
        p=tuple(tuple((int(i==z and j==k)+q[perm[i]][j]-q[i][j])%3 for j in range(b)) for i in range(n))
        gen.append((perm,p))
    return n,es,gen


def audit(n,es,b,gen,use,expected_rank):
    explicit=prepare(n,es,b,gen[:use])
    auto=prepare(n,es,b,permutations=[perm for perm,p in gen[:use]])
    assert explicit.rank==auto.rank==expected_rank
    actual={}
    for ids in matchings(set(range(n)),es):
        actual.setdefault(auto.matching_gain(ids),ids)
    checked=0
    for q in (explicit,auto):
        for t in product(range(3),repeat=b):
            available=next((ids for g,ids in actual.items() if q.project(g)==q.project(t)),None)
            assert (available is not None)==(t in actual)
            if available is not None:
                w=q.repair(available,t)
                assert sorted(v for i in w for v in es[i][:2])==list(range(n)) and q.matching_gain(w)==t
            checked+=1
    return checked


if __name__=='__main__':
    checks=0
    for b in (1,2):
        for gauged in (False,True):
            n,es,gen=hub(b,gauged)
            for k in range(b+1):
                checks+=audit(n,es,b,gen,k,k)
            s,w,d=solve(n,es,(2,)*b,permutations=[v for v,p in gen])
            assert s=='SAT' and d['rank']==b
    # Identity switch realizes periods of a parallel multiset, including duplicates.
    es=[(0,1,(a,0)) for a in (0,1,2,0,1,2)]
    q=prepare(2,es,2,permutations=[(0,1)])
    assert q.rank==1
    for i in range(len(es)):
        for t in range(3):
            ids=q.repair([i],(t,0))
            assert es[ids[0]][2]==(t,0)
    try:
        prepare(2,es[:-1],2,[((0,1),((1,0),(0,0)))])
    except ValueError:
        pass
    else:
        raise AssertionError('multiplicity mismatch accepted')
    assert prepare(2,es[:-1],2,permutations=[(0,1)]).rank==0
    try:
        q.repair([0],(1,2))
    except ValueError:
        pass
    else:
        raise AssertionError('wrong target orbit accepted')
    print(checks,'hub and gauged profile/repair comparisons plus parallel ID and invalid-generator controls passed')
