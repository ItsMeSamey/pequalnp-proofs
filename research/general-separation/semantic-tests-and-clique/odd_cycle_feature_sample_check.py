"""Check every sampled edge-feature set on odd cycles over Q and odd primes."""
from fractions import Fraction
from itertools import product

def edge(t,i,j):
    return int(i==j or i==(j+1)%t)

for t in (3,5,7,9):
    assert all(sum(Fraction(edge(t,i,j),2) for j in range(t))==1 for i in range(t))
    for mask in range((1<<t)-1):
        missing=next(j for j in range(t) if not mask>>j&1)
        dual=[(-1)**((i-missing-1)%t) for i in range(t)]
        response=[sum(w*edge(t,i,j) for i,w in enumerate(dual)) for j in range(t)]
        assert sum(dual)==1 and response[missing]==2
        assert all(v==0 for j,v in enumerate(response) if j!=missing)
        for p in (3,5,7):
            assert sum(dual)%p==1 and response[missing]%p!=0
for x in product(range(2),repeat=10):
    i,h,p0,p1,q0,q1,y0,y1,z0,z1=x
    f=(y0,y1)[(p0,p1)[i]]*(z0,z1)[(q0,q1)[h]]
    total=0
    for a,b in product(range(2),repeat=2):
        rect=int((a,b)==(i,h))*(y0,y1)[(p0,p1)[a]]*(z0,z1)[(q0,q1)[b]]
        tag=min((p0,p1)[1-a]+2*(q0,q1)[1-b],2)
        total+=sum(rect*edge(3,tag,j) for j in range(3))
    assert total==2*f
print('Every proper sample for t=3,5,7,9 and all 1024 two-bank inputs passed')
