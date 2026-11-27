"""Independent deterministic CNF generators; signed one-based literal format."""
from itertools import combinations,product
from random import Random

def corpus():
    rng=Random(8172049)
    for n in (5,7,9,11):
        for rep in range(6):
            clauses=[tuple(rng.choice((-1,1))*v for v in rng.sample(range(1,n+1),3)) for _ in range((427*n+50)//100)]
            yield f'random-{n}-{rep}',n,clauses,'enumerate'
    for k in (3,4,6,8):
        edges=[(2*i,2*((i+1)%k)) for i in range(k)]+[(2*i+1,2*((i+1)%k)+1) for i in range(k)]+[(2*i,2*i+1) for i in range(k)]
        for odd in (0,1):
            clauses=[]
            for v in range(2*k):
                incident=[i+1 for i,e in enumerate(edges) if v in e]
                for a in product((0,1),repeat=3):
                    if sum(a)%2 != int(bool(odd and v==0)):
                        clauses.append(tuple(-x if b else x for x,b in zip(incident,a)))
            yield f'prism-{k}-{odd}',3*k,clauses,'odd-charge' if odd else 'all-zero'
    for holes in (2,3,4,5):
        for extra in (0,1):
            pigeons=holes+extra
            var=lambda i,h:1+i*holes+h
            clauses=[tuple(var(i,h) for h in range(holes)) for i in range(pigeons)]
            clauses += [(-var(i,h),-var(j,h)) for h in range(holes) for i,j in combinations(range(pigeons),2)]
            yield f'holes-{holes}-{extra}',pigeons*holes,clauses,'pigeonhole' if extra else 'diagonal'
    for d in (3,4,8):
        edges=[(i+1,j+1) for i in range(d*d) for j in (i+1,i+d) if j<d*d and (j!=i+1 or j//d==i//d)]
        clauses=[(-a,-b) for a,b in edges]
        for bad in (0,1):
            yield f'grid-{d}-{bad}',d*d,clauses+([(1,),(2,)] if bad else []),'edge-conflict' if bad else 'all-zero'
