"""Brute force matching IDs, congruence feasibility, and original source backlift."""
from itertools import combinations, product
from random import Random
from potential_labelled_matching import search, potentials
from ternary_global_rows import solve

rng=Random(921051)
def matchings(n, edges):
    def visit(free,ids):
        if not free:
            yield ids
            return
        v=min(free)
        for j,(a,b,_) in enumerate(edges):
            if v in (a,b) and {a,b}<=free:
                yield from visit(free-{a,b},ids+(j,))
    return list(visit(set(range(n)),()))

for _ in range(220):
    n=rng.choice((0,2,4,6,8))
    mods=rng.choice([(3,), (4,), (2,3), (3,3), ()])
    pairs=list(combinations(range(n),2))
    edges=[(*rng.choice(pairs),tuple(rng.randrange(q) for q in mods)) for j in range(rng.randrange(13))] if pairs else []
    feasible={tuple(sum(edges[j][2][k] for j in w)%q for k,q in enumerate(mods)) for w in matchings(n,edges)}
    for target in product(*(range(q) for q in mods)):
        status,ids,_=search(n,edges,target,moduli=mods,budget=n)
        assert (status=="SAT")== (target in feasible) and status!="UNKNOWN"
        if ids is not None:
            assert len({v for j in ids for v in edges[j][:2]})==n
            assert tuple(sum(edges[j][2][k] for j in ids)%q for k,q in enumerate(mods))==target

for _ in range(170):
    n=rng.randrange(1,5); q=rng.choice([2,3,4,6])
    pairs=list(combinations(range(n),2))
    edges=[(*rng.choice(pairs),(rng.randrange(q),)) for i in range(rng.randrange(8))] if pairs else []
    cut={v for v in range(n) if rng.randrange(3)==0}
    valid=any(all((u in cut or v in cut or (x[u]+x[v])%q==g[0]) for u,v,g in edges)
              for x in product(range(q),repeat=n))
    p=potentials(n,edges,(q,),cut)
    assert (p is not None)==valid

# All graph labels may be high-dimensional and nonzero even when residuals
# are incident only to a single vertex. Include genuine distinct parallel IDs.
r=41
unit=lambda i:tuple(int(j==i) for j in range(r))
edges=[(2*i,2*i+1,unit(i)) for i in range(10)]
edges.append((0,1,unit(40)))
target=tuple(sum(e[2][j] for e in edges[1:])%3 for j in range(r))
status,ids,stats=search(20,edges,target,budget=1)
assert status=="SAT" and 10 in ids and 0 not in ids and stats['matching_calls']==1
assert search(20,edges,target,budget=0)[0]=="UNKNOWN"
# For S-S edges only the unique owner can report the nonzero gain.
assert search(2,[(0,1,(1,)),(0,1,(2,))],(2,),supplied=(0,1))[:2]==("SAT",(1,))

for _ in range(35):
    n=4
    rows=[tuple(rng.choice((1,2)) for i in range(n)),tuple(rng.randrange(3) for i in range(n))]
    feasible={x for x in product((1,2),repeat=n) if all(sum(a*b for a,b in zip(r,x))%3==0 for r in rows)}
    status,x=solve(n,rows,b=1,h=1,potential_budget=8)
    assert status!="UNKNOWN" and (x in feasible if feasible else status=="UNSAT")
print("220 matching grounds, 170 potential congruences, 35 source charts, rank-41 and ownership controls passed")

for _ in range(150):
    n=rng.choice((0,2,4,6,8)); b=rng.randrange(4)
    pairs=list(combinations(range(n),2))
    edges=[(*rng.choice(pairs),tuple(rng.randrange(3) for _ in range(b)))
           for _ in range(rng.randrange(13))] if pairs else []
    words=matchings(n,edges)
    feasible={tuple(sum(edges[k][2][j] for k in w)%3 for j in range(b)) for w in words}
    target=rng.choice(sorted(feasible)) if feasible and rng.randrange(2) else tuple(rng.randrange(3) for _ in range(b))
    status,ids,metrics=search(n,edges,target,kappa_cap=30)
    assert (status=="SAT")== (target in feasible) and status!="UNKNOWN"
    if "kappa" in metrics:
        assert metrics["matching_calls"]<=3**metrics["kappa"]

r=18
edges=[(i,r+j,tuple(j%3 if k==i else 0 for k in range(r)))
       for i in range(r) for j in range(r)]
for target,expected in [(tuple(i%3 for i in range(r)),"SAT"),((0,)*r,"UNSAT")]:
    status,ids,metrics=search(2*r,edges,target,kappa_cap=0)
    assert status==expected and metrics["kappa"]==0 and metrics["matching_calls"]==1

for x in (1,2):
    # Negative affine-space test can prove absence before the rank cap.
    assert search(2,[(0,1,(0,))],(x,),kappa_cap=0)[0]=="UNSAT"

for _ in range(20):
    n=4
    rows=[tuple(rng.choice((1,2)) for i in range(n)),tuple(rng.randrange(3) for i in range(n))]
    feasible={x for x in product((1,2),repeat=n) if all(sum(a*b for a,b in zip(r,x))%3==0 for r in rows)}
    status,x=solve(n,rows,b=1,h=1,owner_kappa=15)
    assert status!="UNKNOWN" and (x in feasible if feasible else status=="UNSAT")
print("150 ternary owner-rank grounds, two rank-18 one-call cases, and 20 original owner-rank source checks passed")
