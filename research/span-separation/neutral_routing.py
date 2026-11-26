"""Deterministic witness search; terminal top bit is the prescribed w coefficient."""
from functools import lru_cache
from random import Random

def rem(a,b):
    while a.bit_length() >= b.bit_length():
        a ^= b << (a.bit_length()-b.bit_length())
    return a

@lru_cache(None)
def irreducible(d):
    for p in range((1<<d)|1,1<<(d+1),2):
        if all(rem(p,q) for j in range(1,d//2+1) for q in range(1<<j,1<<(j+1))):
            return p
    raise ArithmeticError()

def mul(a,b,p):
    out=0
    while b:
        if b&1: out ^= a
        b >>= 1
        a=rem(a<<1,p)
    return out

def family(m,r):
    if not m:
        yield 0
        return
    d=(m<<r).bit_length()
    p=irreducible(d)
    for beta in range(1<<d):
        powers=[1]
        for _ in range(1,m): powers.append(mul(powers[-1],beta,p))
        for alpha in range(1<<d):
            # All field-linear characters, using binary coordinate functionals.
            yield sum(((alpha&v).bit_count()%2)<<j for j,v in enumerate(powers))

def represent(columns,u):
    piv={}
    for j,v in enumerate(columns):
        mask=1<<j
        while v and v.bit_length() in piv:
            a,b=piv[v.bit_length()]; v^=a; mask^=b
        if v: piv[v.bit_length()]=(v,mask)
    mask=0
    while u:
        if u.bit_length() not in piv: return None
        a,b=piv[u.bit_length()]; u^=a; mask^=b
    return mask

def search(E,m,r,u,candidates=None):
    seen=set()
    for x in family(m,r) if candidates is None else candidates:
        if x in seen: continue
        seen.add(x)
        inds=[i for i,(z,h) in enumerate(E) if (x&z).bit_count()%2==h>>(r-1)]
        cert=represent([(E[i][0]<<r)|E[i][1] for i in inds],u)
        if cert is not None: return x,[i for j,i in enumerate(inds) if cert>>j&1]
    return None

if __name__=='__main__':
    rnd=Random(20261126)
    for _ in range(100):
        m=rnd.randrange(6); r=rnd.randrange(2,5)
        E=[(z,0) for z in range(1,1<<m) if z.bit_count()<=2]
        E += [(rnd.randrange(1<<m),rnd.randrange(1<<r)) for _ in range(rnd.randrange(9))]
        u=rnd.randrange(1<<(r-1))
        sol=search(E,m,r,u)
        assert (sol is None)==(search(E,m,r,u,range(1<<m)) is None)
        if sol is not None:
            x,I=sol; out=0
            for i in I:
                z,h=E[i]; assert (z&x).bit_count()%2==h>>(r-1); out^=(z<<r)|h
            assert out==u
    fam=set(family(5,2))
    for a in range(1,32):
        for b in range(1,32):
            if a!=b:
                assert len({((a&x).bit_count()%2,(b&x).bit_count()%2) for x in fam})==4
    print('100 instances checked, every witness verified, 3720 ordered affine systems hit')
