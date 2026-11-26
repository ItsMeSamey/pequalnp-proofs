from functools import cache
from itertools import combinations
from collections import Counter

edges=[(1<<i)|(1<<j) for i,j in combinations(range(6),2)]
counts=Counter()
for m in (8,9):
    for graph in combinations(edges,m):
        if any(sum(bool(e&(1<<j)) for e in graph)>3 for j in range(6)):
            continue
        positive={e|f for e,f in combinations(graph,2)}
        positive=sorted(x for x in positive if not any(y!=x and y&x==y for y in positive))
        monomials=[x for x in range(1,64) if not any(x&e==x for e in graph)]
        covers={sum(1<<i for i,p in enumerate(positive) if p&x==x) for x in monomials}
        @cache
        def fits(budget,missing):
            if not missing:return True
            if not budget:return False
            bit=missing&-missing
            return any(fits(budget-1,missing&~c) for c in covers if c&bit)
        hit=fits(4,(1<<len(positive))-1)
        counts[m,hit]+=1
print(sorted(counts.items()))
assert sum(counts.values())==1060 and not any(hit for m,hit in counts)
