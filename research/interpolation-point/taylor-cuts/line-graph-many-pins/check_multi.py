from itertools import combinations,product
from collections import Counter
from random import Random
from multigraph import solve_multi

totals=Counter()
def run(n,edges,requests,mode):
    line=[sum(1<<j for j,e in enumerate(edges) if j!=i and set(e)&set(f)) for i,f in enumerate(edges)]
    good={z for z in range(1<<len(edges)) if all(not(z>>i&1) or (z&row).bit_count()%2==0 for i,row in enumerate(line))}
    for ps in requests:
        pi=sum(1<<i for i in ps)
        expected=any(z&pi==pi for z in good)
        result=solve_multi(n,edges,ps)
        assert (result is not None)==expected,(edges,ps,result)
        if result is not None:
            x=sum(1<<i for i in result)
            assert x in good and x&pi==pi
        totals[mode,expected]+=1
for multiplicities in product(range(4),repeat=3):
    edges=[p for p,m in zip(combinations(range(3),2),multiplicities) for _ in range(m)]
    run(3,edges,(ps for k in range(len(edges)+1) for ps in combinations(range(len(edges)),k)),'all-three')
rng=Random(227023)
for _ in range(700):
    n=rng.randrange(3,10)
    edges=rng.choices(list(combinations(range(n),2)),k=rng.randrange(3,13))
    run(n,edges,[rng.sample(range(len(edges)),rng.randrange(min(7,len(edges))+1))], 'sample')
print(totals)
