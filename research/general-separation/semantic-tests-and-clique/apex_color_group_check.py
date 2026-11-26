"""Compare partitioned named/other colors against direct connected components."""
from itertools import combinations,product
from math import prod
from random import Random

def components(vertices,edges):
    cc=[{v} for v in vertices]
    for a,b in edges:
        joined=set.union(*(c for c in cc if a in c or b in c))
        cc=[c for c in cc if not c&joined]+[joined]
    return cc

def partitions(k):
    labels=[0]
    def extend():
        if len(labels)==k:
            yield tuple(labels)
        else:
            for j in range(max(labels)+2):
                labels.append(j)
                yield from extend()
                labels.pop()
    yield from extend()

def check(n,k,edges):
    base=components(range(k,n),[(a,b) for a,b in edges if a>=k])
    cc=components(range(n),edges)
    for q in (0,-1,1,2,3):
        signed=0
        for labels in partitions(k):
            if any(labels[a]!=labels[b] for a,b in edges if b<k):
                continue
            r=max(labels)+1
            subtotal=prod(q-j for j in range(1,r))
            for c in base:
                attached={labels[a] for a,b in edges if a<k and b in c}
                named=sum(all(j==a for a in attached) for j in range(r))
                other=(q-r)*int(not attached)
                subtotal*=named+other
            signed+=subtotal
        assert signed==q**(len(cc)-1)

rng=Random(2731)
count=0
for n,host in [(5,list(combinations(range(5),2))),
               (6,list(product(range(3),range(3,6))))]:
    masks=list(range(1<<len(host)))
    for mask in masks:
        es=[e for j,e in enumerate(host) if mask>>j&1]
        for k in (1,2,3):
            check(n,k,es)
            count+=1
check(3,3,[])
check(3,3,[(0,1),(1,2)])
print(count+2,'rooted host/partition cases across 5 evaluations passed')
