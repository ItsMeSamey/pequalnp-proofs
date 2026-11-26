from itertools import combinations, product
from collections import Counter
from random import Random
from weakmap import attempt, apply, change_basis
from solver import canonical

def yes(T,o,U,pin):
    d=max(t.bit_length() for t in T)
    r=len(canonical(T))
    for h in product(range(1<<d),repeat=2):
        if tuple(apply(h,u) for u in U)!=tuple(pin):
            continue
        if len(canonical(t for t,v in zip(T,o) if apply(h,t)==v))==r:
            return True
    return False

def run():
    rng=Random(1942)
    hist=Counter()
    for i in range(800):
        r=rng.randrange(2,6)
        T=tuple(1<<j for j in range(r))+tuple(rng.randrange(1<<r) for j in range(rng.randrange(6)))
        o=tuple(rng.randrange(4) for t in T)
        a=rng.randrange(1,1<<r)
        U=(a,rng.choice([u for u in range(1,1<<r) if u!=a]))
        pin=tuple(rng.randrange(4) for _ in U)
        status,B=attempt(T,o,U,pin)
        truth=yes(T,o,U,pin)
        if status!='outside binary class':
            assert (status=='yes')==truth
        hist[status,truth]+=1
    T=(1,2,4,8,1,2,3,5,9,12,13)
    o=(1,2,0,0,0,0,0,1,1,0,1)
    status,B=attempt(T,o,(1,2),(0,0))
    assert status=='yes' and len(set(B)-{0,1,2,3})==2
    print('800 equality instances',dict(hist),'F7-containing two-exchange basis',B)
    count=found=0
    for r,n in [(2,3),(3,2)]:
        for aa in range(1<<(r*n)):
            A=tuple((aa>>(r*j))&((1<<r)-1) for j in range(n))
            for bb in range(1<<(r*n)):
                N=tuple((bb>>(r*j))&((1<<r)-1) for j in range(n))
                T=tuple(1<<i for i in range(r))+A
                S=T[:r]+N
                result=change_basis(A,tuple(tuple(x>>i&1 for i in range(r)) for x in N),list(range(r)),list(range(r,r+n)))
                expect=any(len(canonical(T[e] for e in B))==r and len(canonical(S[e] for e in B))<r for B in combinations(range(r+n),r))
                assert (result is not None)==expect
                if result is not None:
                    assert len(canonical(T[e] for e in result))==r and len(canonical(S[e] for e in result))<r
                    found+=1
                count+=1
    print('binary fundamental-matrix pairs',count,'with witnesses',found)

if __name__=='__main__':
    run()
