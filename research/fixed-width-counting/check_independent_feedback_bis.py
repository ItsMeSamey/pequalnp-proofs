"""Count signs in a private-flag layered network and recover independent sets."""
from itertools import product


def binary_rank(rows):
    pivots={}
    for row in rows:
        while row and row.bit_length() in pivots:
            row ^= pivots[row.bit_length()]
        if row:
            pivots[row.bit_length()]=row
    return len(pivots)


def verify(u,v,edges):
    # Independent flags label s -> U, U -> V (one fresh z_e each), V -> t, t -> s.
    s=0; t=u+v+1; d=t+1
    arcs=[(s,i+1) for i in range(u)]+[(1+i,1+u+j) for i,j in edges]+[(1+u+j,t) for j in range(v)]
    k=len(arcs)
    count=0
    phase=0
    flags=0
    for bits in range(1<<k):
        paths=sum(((bits>>i)&(bits>>(u+b))&(bits>>(u+len(edges)+j)))&1
                  for b,(i,j) in enumerate(edges))%2
        count+=paths
        for g in (0,1):
            rows=[1<<a for a in range(d)]
            for j,(a,b) in enumerate(arcs):
                if bits>>j&1:
                    rows[a]^=1<<b
            if g:
                rows[t]^=1<<s
            nullity=d-binary_rank(rows)
            assert nullity==g*paths
            from_kernel=1<<(d+nullity)
            if d<=4:
                direct=0
                for right in range(1<<d):
                    vector=sum(((right&row).bit_count()&1)<<i for i,row in enumerate(rows))
                    direct+=sum((-1)**((left&vector).bit_count()&1) for left in range(1<<d))
                assert direct==from_kernel
            phase+=from_kernel
            flags+=1
    independent=sum(all(not ((left>>i)&(right>>j)&1) for i,j in edges)
                    for left,right in product(range(1<<u),range(1<<v)))
    assert phase==(1<<d)*((1<<(k+1))+count)
    assert 2*count==(1<<len(edges))*((1<<(u+v))-independent)
    return flags


if __name__=='__main__':
    cases=total=0
    for u,v in [(0,0),(1,1),(1,2),(2,1),(2,2),(2,3)]:
        universe=list(product(range(u),range(v)))
        for mask in range(1<<len(universe)):
            edges=[e for i,e in enumerate(universe) if mask>>i&1]
            total+=verify(u,v,edges)
            cases+=1
    print(cases,'bipartite graphs;',total,'independent flag settings')
