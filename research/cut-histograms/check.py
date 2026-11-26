"""Finite arithmetic checks of the residue indicator and Fourier uncertainty."""
from itertools import product
from math import comb
from random import Random

def walsh(v,p):
    v=v.copy()
    d=1
    while d<len(v):
        for i in range(0,len(v),2*d):
            for j in range(i,i+d):
                a,b=v[j],v[j+d]
                v[j],v[j+d]=(a+b)%p,(a-b)%p
        d*=2
    return v

def finite_tests():
    rng=Random(708)
    for p,a in [(2,1),(2,2),(2,3),(3,1),(3,2),(5,1),(7,1)]:
        d=p**a
        for target in range(d):
            tau=(d-1-target)%d
            for N in range(80):
                assert comb(tau+N,d-1)%p==int(N%d==target)
    for _ in range(400):
        r=2*rng.randrange(1,5)
        N=1<<r
        p=rng.choice([3,5,7])
        v=[0]*N
        for i in rng.sample(range(N),rng.randrange(1,N+1)):
            v[i]=rng.randrange(1,p)
        g=walsh(v,p)
        h=[(-1)**sum(((x>>(j*2))&3)==3 for j in range(r//2)) for x in range(N)]
        w=walsh([z*u%p for z,u in zip(g,h)],p)
        s=sum(bool(z) for z in v)
        assert s*sum(bool(z) for z in w)>=N
        if N>s*s:
            assert {h[j] for j in range(N) if g[j]}=={1,-1}
    for _ in range(120):
        n=rng.randrange(1,8)
        edges=[(rng.randrange(n),rng.randrange(n)) for _ in range(rng.randrange(0,6))]
        # Compute Ising partition in F_17 and use the two-edge series formula.
        p=17
        z=3
        same=(1+z*z)%p
        eff=2*z*pow(same,-1,p)%p
        def part(N,es,t):
            return sum(pow(t,sum(((S>>u)^(S>>v))&1 for u,v in es),p)
                       for S in range(1<<N))%p
        sub=[pair for i,(u,v) in enumerate(edges) for pair in ((u,n+i),(n+i,v))]
        assert part(n+len(edges),sub,z)==pow(same,len(edges),p)*part(n,edges,eff)%p
    print("Lucas residue identities, 400 quadratic uncertainty cases, and 120 subdivision identities passed")
if __name__=="__main__":
    finite_tests()
