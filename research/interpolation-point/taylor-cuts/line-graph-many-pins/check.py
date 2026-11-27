from itertools import combinations
from collections import Counter
from random import Random
from solver import solve

totals=Counter()
rng=Random(22702)
def check(n,edges,requests,group):
    neighbor=[sum(1<<j for j,e in enumerate(edges) if i!=j and set(f)&set(e)) for i,f in enumerate(edges)]
    valid=[z for z in range(1<<len(edges)) if all((z>>i&1)==0 or not ((neighbor[i]&z).bit_count()%2) for i in range(len(edges)))]
    for pins in requests:
        pm=sum(1<<i for i in pins)
        expected=any(mask&pm==pm for mask in valid)
        witness=solve(n,edges,pins)
        assert (witness is not None)==expected,(edges,pins,witness)
        if witness is not None:
            actual=sum(1<<i for i in witness)
            assert actual in valid and actual&pm==pm
        totals[group,len(pins),expected]+=1

for n in range(2,6):
    all_edges=list(combinations(range(n),2))
    for mask in range(1<<len(all_edges)):
        es=[e for i,e in enumerate(all_edges) if mask>>i&1]
        check(n,es,(ps for k in (4,5) for ps in combinations(range(len(es)),k)),'all-small')
base=[(0,1),(0,2),(3,4),(3,5)]
other=[e for e in combinations(range(6),2) if e not in base]
for mask in range(1<<len(other)):
    es=base+[e for i,e in enumerate(other) if mask>>i&1]
    check(6,es,[(0,1,2,3)],'all-two-cherries')
for _ in range(75):
    n=rng.randrange(6,10); all_edges=list(combinations(range(n),2))
    es=rng.sample(all_edges,rng.randrange(6,min(13,len(all_edges))+1))
    check(n,es,[rng.sample(range(len(es)),k) for k in (4,5,6)],'sample')
print(totals)
