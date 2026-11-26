from itertools import combinations
from random import Random
rng=Random(6421)
def rank(rows,p):
    basis={}
    for row in rows:
        a=list(row)
        for j,b in sorted(basis.items()):a=[(u-a[j]*v)%p for u,v in zip(a,b)]
        j=next((i for i,x in enumerate(a) if x),None)
        if j is not None:basis[j]=[x*pow(a[j],-1,p)%p for x in a]
    return len(basis)
for trial in range(60):
    k=2+trial%2
    # Actual row and column enumeration with two representatives per color.
    n=2*k
    pairs=list(combinations(range(n),2))
    forbidden={(i,j) for i,j in pairs if i//2==j//2 or rng.randrange(2)}
    rows=[]; supports=set()
    for x in range(1<<n):
        if any(x>>i&1 and x>>j&1 for i,j in forbidden): continue
        U=0
        for i in range(n):
            if x>>i&1:U|=1<<(i//2)
        supports.add(U)
        rows.append([int((U&y)==0) for y in range(1<<k)])
    assert (len(supports)==1<<k)==((1<<k)-1 in supports)
    for p in (2,3,5):assert rank(rows,p)==len(supports)
print('180 direct graph-matrix ranks verified over F2,F3,F5')
