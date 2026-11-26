from itertools import product
from math import ceil,log2
from functools import cache
def rank(rows,p):
    basis={}
    for row in rows:
        a=list(row)
        for j,b in sorted(basis.items()):
            a=[(x-a[j]*y)%p for x,y in zip(a,b)]
        j=next((i for i,x in enumerate(a) if x),None)
        if j is not None:basis[j]=[x*pow(a[j],-1,p)%p for x in a]
    return len(basis)
for flat in product((0,1),repeat=12):
    rows=[flat[i:i+4] for i in (0,4,8)]
    criterion=min(len({v for v in rows if any(v)}),len({v for v in zip(*rows) if any(v)}))<=2
    assert all((rank(rows,p)<=2)==criterion for p in (3,5))
for n in range(1,14):
    for w in (1,2,3):
        @cache
        def width(l,r):
            values=[tuple(int(i>=j) for i in range(l,r)) for j in range(l,r+1)]
            rows=sorted({x[::2] for x in values}); cols=sorted({x[1::2] for x in values})
            entries={(x[::2],x[1::2]) for x in values}
            return rank([[int((a,b) in entries) for b in cols] for a in rows],3)
        @cache
        def depth(l,r):
            if width(l,r)<=w:return 0
            return 1+min(max(depth(l,i),depth(i+1,r)) for i in range(l,r))
        assert depth(0,n)==max(0,ceil(log2((n+1)/(2*w))))
        best=n
        for mask in range(1<<n):
            if mask.bit_count()>=best:continue
            fixed=[-1]+[i for i in range(n) if mask>>i&1]+[n]
            if all(width(a+1,b)<=w for a,b in zip(fixed,fixed[1:])):best=mask.bit_count()
        assert best==n//(2*w)
print('4096 Boolean matrices over each of F3/F5 and 39 chain selector/depth optima verified')
