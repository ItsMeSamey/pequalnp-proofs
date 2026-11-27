from itertools import product, permutations, combinations
from check_artificial_rebases import apply
from random import Random

def labs(p):
    d={}
    for i in range(len(p)):
        j=i
        while j not in d:
            d[j]=i
            j=p[j]
    return [d[i] for i in range(len(p))]

def merge(d,pairs):
    d=d.copy()
    for a,b in pairs:
        u,v=d[a],d[b]
        d=[v if z==u else z for z in d]
    return d

phys=((0,1,2),(1,2,0))
fake=((1,0,2),(0,2,1),(2,1,0))
rng=Random(379)
cases=list(permutations(range(6)))+[rng.sample(range(9),9) for _ in range(150)]
queries=cores=branches=0
for p in cases:
    n=len(p)//3
    for b in product(range(3),repeat=n):
        raw=apply(p,b,fake)
        d=labs(raw)
        pairs=[[tuple(i for i in range(g*3,g*3+3) if fake[b[g]][i%3]!=h[i%3]) for h in phys] for g in range(n)]
        ds={}
        for mask in range(1<<n):
            q=merge(d,[a for g in range(n) if mask>>g&1 for a in pairs[g]])
            ds[mask]=mask.bit_count()+len(set(q))-len(set(d))
        maximum=max(ds.values())
        opts=[m for m,v in ds.items() if v==maximum]
        K=(1<<n)-1
        for m in opts:K &= m
        if K not in opts:raise AssertionError('intersection')
        inside=[g for g in range(n) if K>>g&1]
        outside=[g for g in range(n) if not K>>g&1]
        q=merge(d,[a for g in inside for a in pairs[g]])
        forests=[s for s in product(range(2),repeat=len(outside)) if len(set(q))-len(set(merge(q,[pairs[g][h] for g,h in zip(outside,s)])))==len(outside)]
        if not forests:raise AssertionError('no outside forest')
        for pins in product(range(2),repeat=len(inside)):
            r=raw.copy()
            for g,h in zip(inside,pins):
                r[3*g:3*g+3]=[p[3*g+j] for j in phys[h]]
            d2=labs(r)
            if any(len(set(d2))-len(set(merge(d2,[pairs[g][h] for g,h in zip(outside,s)])))!=len(outside) for s in forests):
                raise AssertionError('lost forest')
            branches+=1
        cores+=bool(K)
        queries+=1
print(queries,'references;',cores,'nonempty cores;',branches,'pinned branches')
