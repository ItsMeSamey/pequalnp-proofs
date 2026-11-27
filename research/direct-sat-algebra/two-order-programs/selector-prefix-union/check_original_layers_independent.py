"""Original truth-table oracle for each prefix image and joint translation group."""
from random import Random
from prefix_union import solve


def sat(clauses,x):
    return all(any(bool(x >> (abs(l)-1)&1)==(l>0) for l in c) for c in clauses)


def verify(n,clauses):
    blocks={}
    for c in clauses:
        if not any(-l in c for l in c):
            ids=frozenset(abs(l)-1 for l in c)
            blocks.setdefault(ids,[]).append(c)
    groups=list(blocks.items())
    results=solve(n,clauses,inspect=True)
    prefix=[]
    actual_sat=any(sat(clauses,x) for x in range(1<<n))
    assert (results['status']=='sat')==actual_sat
    if actual_sat: assert sat(clauses,results['witness'])
    active=set(range(1<<n))
    sym=set(range(1<<n))
    seen=set()
    for i,(sites,group) in enumerate(groups):
        accepted={x for x in range(1<<n) if sat(group,x)}
        sym={s for s in sym if all((x^s) in accepted for x in accepted)}
        active &= accepted
        seen.update(sites)
        future=set().union(*(tail for tail,_ in groups[i+1:]))
        mask=sum(1<<v for v in seen & future)
        front,basis,keys=results['layers'][i]
        projected={s&mask for s in sym}
        span={0}
        for b in basis:
            assert b not in span
            span |= {x^b for x in span}
        assert mask==front and span==projected
        possible={x&mask for x in active}
        wanted={min(x^s for s in projected) for x in possible}
        assert len(keys)==len(set(keys)) and set(keys)==wanted
        assert {k^s for k in keys for s in projected}==possible
        prefix.append((len(span),len(keys)))
        if not active:break
    assert len(results['layers'])==len(prefix)
    return prefix


fixtures=[
    (3,[(1,-2),(-1,2),(2,3),(2,),(-3,)]),
    (4,[(1,-2),(-1,2),(2,-3),(-2,3),(3,-4),(-3,4),(4,)]),
    (3,[(1,2,3),(1,-2,-3),(-1,2,-3),(-1,-2,3),(1,-2),(2,3)]),
    (3,[(1,2),(-2,1),(2,3),(-1,-2),(2,-2),(-3,)]),
    (2,[(-1,2),(1,-2),(1,),(-2,)]),
    (2,[(),(1,-2)]),
    (4,[(1,-1),(2,2,2)]),
    (0,[])]
rng=Random(93018)
for _ in range(196):
    n=rng.randrange(2,8)
    scopes=[rng.sample(range(1,n+1),rng.randrange(1,min(3,n)+1)) for _ in range(rng.randrange(2,9))]
    clauses=[tuple(v if rng.randrange(2) else -v for v in rng.choice(scopes)) for _ in range(rng.randrange(3,16))]
    fixtures.append((n,clauses))
layers=multi=nontrivial=0
for n,clauses in fixtures:
    history=verify(n,clauses)
    layers+=len(history)
    multi+=sum(k>1 for _,k in history)
    nontrivial+=sum(a>1 for a,_ in history)
assert multi and nontrivial
print(len(fixtures),"CNFs;",layers,"layers;",multi,"multi-orbit layers;",nontrivial,"nontrivial frontier groups")
