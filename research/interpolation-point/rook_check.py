from fractions import Fraction as F
from itertools import product, permutations, combinations
from math import prod, factorial, comb
def per(M):
    n=len(M)
    return sum(prod(M[i][j] for i,j in enumerate(p)) for p in permutations(range(n)))
for m in range(1,4):
    x=[13+2*i for i in range(m)]; y=[-i for i in range(m)]
    C=[[F(1,a+b) for b in y] for a in x]
    rook=[sum(per([[C[i][j] for j in J] for i in I]) for I in combinations(range(m),h) for J in combinations(range(m),h)) for h in range(m+1)]
    for K in (m,m+1):
        for z in (-2,1,3):
            direct=sum(prod(1+z*sum(C[i][j] for j,k in enumerate(f) if k==i) for i in range(m)) for f in product(range(K),repeat=m))
            assert direct==sum(z**h*K**(m-h)*v for h,v in enumerate(rook))
    vals=[[] for _ in rook]
    for R in range(30,30+2*m+1):
        S=[]
        for k in range(m+1):
            B=[[F(1,a+b) for b in y+[R]*k] for a in x+[R]*k]
            residual=per(B)-sum(F(factorial(k)**2,factorial(k-j))*F(1,2*R)**(k-j)*S[j] for j in range(k))
            S.append(residual/factorial(k)**2)
            vals[k].append(S[k]*prod(R+a for a in x)*prod(R+b for b in y))
    for j,vs in enumerate(vals):
        deg=2*(m-j)
        lead=sum((-1)**(deg-t)*comb(deg,t)*vs[t] for t in range(deg+1))/factorial(deg)
        assert lead==rook[m-j]
print('Exact packet placement, augmented permanent, and all rook coefficients verified for m=1,2,3')
def det(a):
    a=[r[:] for r in a]; d=F(1)
    for j in range(len(a)):
        i=next((i for i in range(j,len(a)) if a[i][j]),None)
        if i is None:return 0
        if i!=j:a[i],a[j]=a[j],a[i];d=-d
        pivot=a[j][j];d*=pivot
        for i in range(j+1,len(a)):
            q=a[i][j]/pivot
            for l in range(j,len(a)):a[i][l]-=q*a[j][l]
    return d
for m in range(1,6):
    C=[[F(1,30+2*i-j) for j in range(m)] for i in range(m)]
    rook=[sum(per([[C[i][j] for j in J] for i in I]) for I in combinations(range(m),h) for J in combinations(range(m),h)) for h in range(m+1)]
    for z in (-4,-1,0,1,2,9):
        assert det([[z*v+v*v for v in row] for row in C])/det(C)==sum(z**(m-h)*v for h,v in enumerate(rook))
print('30 exact direct-determinant polynomial controls passed')
