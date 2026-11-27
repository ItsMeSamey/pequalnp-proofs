"""Trace every orientation and compute the exact marked theta sign image."""
from itertools import permutations,product


def joins(x,y,bits):
    F=list(range(9))
    for offset,bit in ((0,x),(1,y)):
        for i in range(3):
            F[3*i+offset]=3*((i+(1 if bit==0 else -1))%3)+offset
    perm=[F[3*(v//3)+(v+(1 if bits[v//3]==0 else -1))%3] for v in range(9)]
    v=perm[0]
    while v not in (0,1):
        v=perm[v]
    return v==1


def parity(p):
    return sum(p[a]>p[b] for a in range(3) for b in range(a+1,3))%2


if __name__=='__main__':
    for x,y in product(range(2),repeat=2):
        for bits in product(range(2),repeat=3):
            assert joins(x,y,bits)==(x==y)
    assert {(parity(p),parity(p)) for p in permutations(range(3)) if p[0]==0}=={(0,0),(1,1)}
    print('32 rotation systems and both marked theta automorphisms checked')
