"""All disjoint support pairs under seeded four-bit maps on exchange-pair examples."""
from random import Random
from collections import defaultdict
rng=Random(117)
def span(v):
    a=[0]
    for x in v:
        a += [y^x for y in a]
    return a
hits=best=0
for k in range(2,6):
    for trial in range(1000):
        rows=list(range(k))
        rng.shuffle(rows)
        rows=[1<<i for i in rows]
        if trial%2:
            for j in range(0,k-2,2):
                for i in (0,1):
                    rows[i]^=3<<j
        cuts=span([(1<<i)|(row<<k) for i,row in enumerate(rows)])
        cycles=span([(1<<(k+j))|sum(((row>>j)&1)<<i for i,row in enumerate(rows)) for j in range(k)])
        full=(1<<(2*k))-1
        bicycles=set(cuts)&set(cycles)
        if full not in bicycles: continue
        alpha,beta=(span([rng.randrange(16) for _ in range(2*k)]) for j in range(2))
        cells=defaultdict(list)
        for c in cycles:
            for d in cuts:
                if not c&d: cells[alpha[c]^beta[d]].append((c,d))
        if len(cells)==16: continue
        for a in bicycles-{0,full}:
            b=full^a
            if cells[alpha[a]^beta[b]]!=[(a,b)] or cells[alpha[b]^beta[a]]!=[(b,a)]: continue
            hits+=1
            n=sum(not(c&~a) for c in cycles).bit_length()-1
            t=sum(not(d&~b) for d in cuts).bit_length()-1
            best=max(best,n+t)
            assert n+t<=3 and len(bicycles)<=8
print(hits,best)
