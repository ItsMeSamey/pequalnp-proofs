"""Check programmed Appendix D Cauchy packet roots against direct formulas."""
from fractions import Fraction
from itertools import permutations,product
from math import prod
from random import Random

def kernel(L,T,x,y):
    return Fraction(prod(T-q for q in range(1-L,L) if q!=y-x),
                    prod(-q for q in range(1-L,L) if q!=0))

def residue(x,p):
    modulus=1<<p
    return (x.numerator*pow(x.denominator,-1,modulus))%modulus

def det(a):
    n=len(a)
    return sum((-1)**sum(s[i]>s[j] for i in range(n) for j in range(i+1,n))*
               prod(a[i][s[i]] for i in range(n)) for s in permutations(range(n)))

def per(a):
    return sum(prod(row[j] for row,j in zip(a,perm)) for perm in permutations(range(len(a))))

def cnf_test(n,clauses,L):
    slots=[2+2*j for j in range(n)]
    row=0; T=2*L+1
    wk=[kernel(L,T,row,y) for y in slots]
    scales=[T-y+row for y in slots]
    N=wk[0]*scales[0]
    cleared=0; actual=0; sat=0
    dens=[prod(scales[j] for j,sign in cl) for cl in clauses]
    for bits in product(range(2),repeat=n):
        vals=[[(j,sign) for j,sign in cl if bits[j]^sign] for cl in clauses]
        sat+=all(vals)
        actual+=prod(sum(wk[j] for j,sg in yes) for yes in vals)
        cleared+=prod(sum(d//scales[j] for j,sg in yes) for yes,d in zip(vals,dens))
    assert actual==N**len(clauses)*cleared/prod(dens)
    assert cleared<=2**n*(3*(3*L+1)**2)**len(clauses)
    p=len(clauses)*L.bit_length()+(2**n*(3*(3*L+1)**2)**len(clauses)).bit_length()+1
    assert bool(residue(actual,p))==bool(sat)
    assert all(kernel(L,0,row,y)==0 for y in slots)
    return sat

rng=Random(813)
sats=[]
for _ in range(120):
    n=4; m=rng.randrange(1,10)
    clauses=[[(j,rng.randrange(2)) for j in rng.sample(range(n),rng.randrange(1,4))] for _ in range(m)]
    sats.append(cnf_test(n,clauses,16))
sats.append(cnf_test(2,[[(0,0)],[(0,1)]],8))
assert 0 in sats and max(sats)>0
for m in range(1,6):
    L=16; T=2*L+1; xs=list(range(m)); ys=[2*j for j in range(m)]
    N=kernel(L,T,0,0)*T
    C=[[Fraction(1,T+x-y) for y in ys] for x in xs]
    W=[[kernel(L,T,x,y) for y in ys] for x in xs]
    assert per(W)==N**m*det([[v*v for v in row] for row in C])/det(C)
    for _ in range(10):
        mask=[[rng.randrange(2) for _ in range(m)] for _ in range(m)]
        local=[[kernel(L,T,0,ys[j])*mask[i][j] for j in range(m)] for i in range(m)]
        assert per(local)==per(mask)*prod(kernel(L,T,0,y) for y in ys)
print("121 programmed CNFs, five Borchardt identities, and 50 masked permanent scales passed")
