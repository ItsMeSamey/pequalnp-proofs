"""Check the projection bitmaps and grouped ORs of retained transcript leaves."""
from collections import defaultdict
from itertools import product
from math import log2
from random import Random

def grouped(word, allowed, count, width):
    # Each block table contains all ORs of its one-hot wires.
    for start in range(0,count,width):
        mask=sum(1<<(a-start) for a in allowed if start<=a<start+width)
        wires=[int(word==a) for a in range(start,min(count,start+width))]
        table=[0]
        for wire in wires:
            table += [v|wire for v in table]
        if table[mask]: return 1
    return 0

rng=Random(202)
for _ in range(40):
    side=8
    # Full transcript controls party choice and query table.
    nodes=[(rng.randrange(2),rng.randrange(1<<side)) for i in range(31)]
    terminal=[rng.randrange(2) for i in range(32)]
    buckets=defaultdict(set)
    for a,b in product(range(side),repeat=2):
        i=0
        for j in range(5):
            owner,t=nodes[i]
            bit=(t>>(b if owner else a))&1
            i=2*i+1+bit
        if terminal[i-31]:
            buckets[i].add((a,b))
    order=sorted(buckets,key=lambda i:-len(buckets[i]))
    total=sum(map(len,buckets.values()))
    ent=sum(len(s)/total*log2(total/len(s)) for s in buckets.values())
    for k in range(1,side+1):
        keep=order[:k]
        expected=set.union(set(),*(buckets[i] for i in keep))
        actual=set()
        for a,b in product(range(side),repeat=2):
            if any(grouped(a,{u for u,v in buckets[i]},side,max(1,k.bit_length()-1)) and
                   grouped(b,{v for u,v in buckets[i]},side,max(1,k.bit_length()-1)) for i in keep):
                actual.add((a,b))
        assert actual==expected and total-len(actual)<=total*ent/log2(k+1)+1e-8
print('320 protocol/retention cases, all half-addresses passed')
