from collections import Counter
from itertools import combinations
from random import Random
rng=Random(701)
for sample in range(90):
    n=rng.randrange(2,8)
    p=31
    # Every positive two-clause in a clique. E=t(t-1)/2 for t false bits.
    # Its quadratic lift has rank one after a free diagonal change.
    core=list(combinations(range(n),2))
    defects=[[(rng.randrange(n),rng.randrange(2)) for _ in range(rng.randrange(n+1))] for _ in range(rng.randrange(5))]
    exact=sum(all((a>>i&1) or (a>>j&1) for i,j in core) and all(any((a>>i&1)==v for i,v in clause) for clause in defects) for a in range(1<<n))
    total=0
    for mask in range(1<<len(defects)):
        pins={}
        ok=True
        for j,clause in enumerate(defects):
            if mask>>j&1:
                for i,v in clause:
                    if i in pins and pins[i]==v: ok=False
                    pins[i]=1-v
        if not ok: continue
        states={0:1}
        for i in range(n):
            new=Counter()
            for t,m in states.items():
                for bit in ([pins[i]] if i in pins else (0,1)):
                    new[(t+1-bit)%p]+=m
            states=new
        total+=(-1)**mask.bit_count()*sum(m for t,m in states.items() if t*(t-1)%p==0)
    assert total==exact
print('90 rank-one clique CNFs with arbitrary defective clauses verified')
