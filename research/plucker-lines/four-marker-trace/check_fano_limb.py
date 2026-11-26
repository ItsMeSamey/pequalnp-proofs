from random import Random
from check_virtual_sums import models
C=[1,2,3,4,5,6,7]
code=[(c,d,(c>>6&1)+2*(d>>6&1)) for c,d,_ in models(C,[0]*7,[0]*7,3)]
def table(a,b):
    T=[set() for _ in range(3)]
    for c,d,m in code:
        s=0
        for i in range(6):
            if c>>i&1:s^=a[i]
            if d>>i&1:s^=b[i]
        T[m].add(s)
    return T
def eligible(T):
    for i,S in enumerate(T):
        for a in S:
            if not any(all(any((b^h) in K for b in K) for K in T) for h in [a^c for c in S if c!=a]):return False
    return True
if __name__=='__main__':
    rng=Random(15732)
    for _ in range(100000):
        a,b=([rng.randrange(4) for _ in range(6)] for __ in range(2))
        L=table(a,b)
        if min(map(len,L))>=3 and min(map(len,L))<4 and len(set(map(frozenset,L)))>=2:
            assert eligible(L)
            break
    for _ in range(25000):
        u,v=([rng.randrange(16) for _ in range(6)] for __ in range(2))
        R=table(u,v)
        actual=set().union(*[{x^y for x in X for y in Y} for X,Y in zip(L,R)])
        if len(actual)==15:break
    print('leaf',a,b,[sorted(S) for S in L])
    print('core',u,v,[sorted(S) for S in R], 'missing', sorted(set(range(16))-actual))
    from connected_hole import connected
    E=[1,2,3,4,5,6,8,16,24,31,23,15]
    assert {z for _,_,z in models(E,a+u,b+v,5)}==set(range(16))-{10}
    for i,e in enumerate(E):
        rest=E[:i]+E[i+1:];mask=e&-e
        assert connected(rest) and connected([v^(e if v&mask else 0) for v in rest])
    print('Direct raw image and 24 elementary minors agree.')
