"""Formal-degree-three closure check on the thirty affine four-bit hyperplanes."""
from itertools import combinations
from collections import Counter

TERMS = [sum(1 << j for j in sub) for k in range(4) for sub in combinations(range(4),k)]
INDEX = {m:i for i,m in enumerate(TERMS)}


def coefficients(fn):
    v=[fn(x) for x in range(16)]
    for j in range(4):
        for x in range(16):
            if x & (1<<j):
                v[x] ^= v[x ^ (1<<j)]
    assert not v[15]
    return sum(1<<INDEX[m] for m in TERMS if v[m])


def reduce_row(p,space):
    while p and p.bit_length() in space:
        p ^= space[p.bit_length()]
    return p


def insert(p,space):
    p=reduce_row(p,space)
    if p:
        space[p.bit_length()] = p
    return p


def closure(*polys):
    basis={}
    queue=list(polys)
    for p in queue:
        p=insert(p,basis)
        if p and TERMS[p.bit_length()-1].bit_count()<3:
            for j in range(4):
                v=0
                for i,m in enumerate(TERMS):
                    if p>>i&1:
                        v ^= 1<<INDEX[m|(1<<j)]
                queue.append(v)
    return basis


def affine(a,b,x):
    return ((a&x).bit_count()&1)^b


def Q(x):
    return ((x&(x>>2)&3).bit_count()&1)


def main():
    summary=Counter()
    for a in range(1,16):
        for b in (0,1):
            pts=[x for x in range(16) if affine(a,b,x)==0 and not Q(x)]
            z=next((u,c) for u in range(16) for c in (0,1)
                   if all(not(x>>2) or affine(u,c,x)==(x&1)*((x>>2)&1) for x in pts))
            B=closure(coefficients(Q),coefficients(lambda x:affine(a,b,x)))
            # All low-degree vanishing functions, independent of selection of z.
            ev={}
            for m in TERMS:
                if m.bit_count()<=2:
                    insert(sum(1<<i for i,x in enumerate(pts) if x&m==m),ev)
            van_dim=11-len(ev)
            low=sum(TERMS[k-1].bit_count()<=2 for k in B)
            assert low==van_dim
            def gs(x):
                s0,s1=x&1,(x>>1)&1
                t0,t1=(x>>2)&1,(x>>3)&1
                r=affine(*z,x)
                return ((s0^r)*t0,(s1^r)*t1,r*(t0^t1))
            assert all(not reduce_row(coefficients(lambda x:gs(x)[i]),B) for i in range(3))
            affrank={}
            for x in pts:
                insert(16|x,affrank)
            summary[len(pts),len(affrank),van_dim]+=1
    print(dict(summary))


if __name__=="__main__":
    main()
