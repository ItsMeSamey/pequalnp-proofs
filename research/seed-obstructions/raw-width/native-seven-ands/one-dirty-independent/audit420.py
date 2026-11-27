from cuts import load
from itertools import combinations
pos,neg=load(())
def sig(r):
    return frozenset(i for i in range(20) if r>>i&1)
P={sig(r) for r in pos}
N={sig(r) for r in neg}
def choices(xs):
    for k in range(2,len(xs)+1):
        for t in combinations(xs,k):
            yield frozenset(t)
def neighbors(v):
    return set().union(*(e-{v} for e in P if v in e))
rows=set()
for e in P:
    p,t=sorted(e)
    for A in choices(neighbors(t)):
        for B in choices(neighbors(p)):
            if not (p in A and t in B): continue
            unsafe=[r for r in N if r&A and r&B]
            G=set(range(20))-set().union(*unsafe)
            gp={x for x in G if x<13}
            gt=G-gp
            assert A&gp=={p} and B&gt=={t}
            S=B if len(B)>2 else B-{t}
            for r in N:
                assert not (r&gp and r&S or t in r and r&A)
            for r in P:
                if r&A and r&B and r&G:
                    assert r&gp and r&S or t in r and r&A
            rows.add((A,B))
assert len(rows)==420
print('420 distinct arm pairs,',len(P),'positive and',len(N),'distinct negative projections')
