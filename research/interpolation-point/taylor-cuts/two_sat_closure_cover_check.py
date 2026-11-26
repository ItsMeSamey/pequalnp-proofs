from itertools import combinations,product
from random import Random
from two_sat_closure_cover import solve,minimum_cover,interactions
from bijunctive_xor_hull import solve as raw_peel


def check(n,clauses,rows):
    valid={x for x in range(1<<n)
           if all(any(bool(x>>(abs(l)-1)&1)==(l>0) for l in c) for c in clauses)
           and all((x&a).bit_count()%2==b for a,b in rows)}
    x,s=solve(n,clauses,rows)
    assert (x in valid) if valid else x is None
    return s


def main():
    base=[(a,b) for a in (-1,1) for b in (-2,2)]+[(1,),(-1,)]
    for pattern in range(64):
        clauses=[c for i,c in enumerate(base) if pattern>>i&1]
        for a,b in product((0,1),repeat=2):
            check(2,clauses,[(1,a),(2,b)])
    rng=Random(319)
    for _ in range(140):
        n=rng.randrange(1,7)
        clauses=[tuple(rng.choice((-1,1))*rng.randrange(1,n+1) for j in range(2))
                 for i in range(rng.randrange(12))]
        rows=[(rng.randrange(1<<n),rng.randrange(2)) for j in range(rng.randrange(7))]
        check(n,clauses,rows)
    # The equivalent active pair (a,b) receives one XOR label twice,
    # removing the whole common support from the interaction graph.
    clauses=[(-1,3),(-2,4),(-3,4),(-4,3)]
    stats=check(4,clauses,[(12,0),(1,1),(2,1)])
    assert stats["cancelled_signatures"]==1 and stats["cover_size"]==0
    # Rank can grow arbitrarily with vertex-cover size one.
    n=24
    star=[(-1,-j) for j in range(2,n+1)]
    x,s=solve(n,star,[(1<<j,int(j!=0)) for j in range(n)])
    assert x==(1<<n)-2 and s["cover_size"]==1 and s["xor_rank"]==n
    # Raw SCC affine-hull peeling stalls on the connected star.
    labels=[1,2]+[0]*(n-2)
    assert raw_peel(n,star,labels,3)[0]=="UNKNOWN"
    x,s=solve(n,star,[(1,1),(2,1)])
    assert x is None and s["cover_size"]==1
    print("396 exhaustive/random CNF checks; cancelled support; rank-24 star; stalled raw SCC control")


if __name__=='__main__':
    main()
