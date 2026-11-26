from independent import src
from high_one_nonempty import CS,counts
from itertools import product,combinations
want=[sum(1<<v for v in group) for k in (1,2) for group in combinations(range(8),k)]
assert sorted(want)==sorted(CS) and len(CS)==len(set(CS))==36
total=0
for v,d,r,q in product(range(8),range(5),range(2),range(5)):
    bank=counts(v,d,r,q)
    for j,c in enumerate(CS):
        # If this support receives X, it can save at most the number of occurrences
        # routed there; otherwise all local direct and marked demands survive.
        copies=0 if not ((c>>v)&1) else (2 if c.bit_count()==1 else 1)
        cost=max(q,d-copies) if copies else max(d,r)
        for threshold,mask in enumerate(bank,1):
            assert bool(mask & (1<<j))==(cost>=threshold)
            total+=1
print('recipient-support cost table entries checked',total)
