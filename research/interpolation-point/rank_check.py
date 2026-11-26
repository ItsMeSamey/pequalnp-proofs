from itertools import product
from random import Random
rng=Random(611)
p=3
def elim(a,i,j):
    return [[(a[u][v]-a[u][j]*pow(a[i][j],-1,p)*a[i][v])%p for v in range(len(a[0])) if v!=j] for u in range(len(a)) if u!=i]
def rank(a):
    r=0
    while a:
        pivot=next(((i,j) for i,row in enumerate(a) for j,val in enumerate(row) if val),None)
        if pivot is None: break
        a=elim(a,*pivot)
        r+=1
    return r
for n in range(2,7):
    for _ in range(10):
        a=[[0]*n for _ in range(n)]
        for i in range(n):
            for j in range(i): a[i][j]=a[j][i]=rng.randrange(p)
        b=[row[:] for row in a]
        rr=list(range(n)); cc=rr[:]; used=set()
        while True:
            pivot=next(((i,j) for i,u in enumerate(rr) for j,v in enumerate(cc) if u!=v and u not in used and v not in used and b[i][j]),None)
            if not pivot: break
            i,j=pivot
            used.update((rr[i],cc[j]))
            b=elim(b,i,j)
            rr.pop(i); cc.pop(j)
        t=len(used)//2
        d=[0]*n
        for v in set(range(n))-used: d[v]=-b[rr.index(v)][cc.index(v)]%p
        def fill(d):return [[a[i][j] if i!=j else d[i] for j in range(n)] for i in range(n)]
        opt=min(rank(fill(v)) for v in product(range(p),repeat=n))
        assert t<=opt<=rank(fill(d))<=3*t
print('50 rank certificates checked against exhaustive optimal diagonals')
