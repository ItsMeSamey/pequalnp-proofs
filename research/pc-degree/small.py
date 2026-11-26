"""Check six-vertex bipartite graphs up to within-side permutations and RREF marker bases."""
from itertools import combinations, permutations, product
from collections import Counter
from check import pc


def bases(n):
    for rank in range(1,4):
        for pivots in combinations(range(n),rank):
            free = [(i,j) for i,p in enumerate(pivots) for j in range(p+1,n)
                    if j not in pivots]
            for bits in range(1<<len(free)):
                rows = [1<<p for p in pivots]
                for a,(i,j) in enumerate(free):
                    rows[i] |= ((bits>>a)&1)<<j
                yield rank, [sum(((v>>j)&1)<<i for i,v in enumerate(rows))
                             for j in range(n)]


def graphs(k,m):
    seen=set()
    for bits in range(1<<(k*m)):
        if bits in seen:
            continue
        a=[(bits>>(i*m))&((1<<m)-1) for i in range(k)]
        rows=[r<<k for r in a]+[sum(((r>>j)&1)<<i for i,r in enumerate(a)) for j in range(m)]
        yield rows
        for p in permutations(range(m)):
            b=[sum(((r>>j)&1)<<p[j] for j in range(m)) for r in a]
            seen.update(sum(v<<(i*m) for i,v in enumerate(s)) for s in permutations(b))


def run():
    n=6
    tables=[]
    for rank,labels in bases(n):
        vals=[0]*(1<<n)
        for x in range(1,1<<n):
            b=x&-x
            vals[x]=vals[x^b]^labels[b.bit_length()-1]
        tables.append((rank,labels,vals))
    outcomes=Counter()
    for k in range(1,4):
        for rows in graphs(k,n-k):
            feasible=[x for x in range(1<<n) if all(not(x>>i&1) or not((x&r).bit_count()&1)
                                                    for i,r in enumerate(rows))]
            for rank,labels,vals in tables:
                for z in set(range(1<<rank))-{vals[x] for x in feasible}:
                    d=2
                    while not pc(rows,labels,z,d,rank):
                        d+=1
                    outcomes[d]+=1
                    if d>=3 and outcomes[d]==1:
                        print("sample",rows,labels,z,d,flush=True)
        print("split",k,"cumulative",dict(outcomes),flush=True)
    return outcomes


if __name__ == "__main__":
    run()
