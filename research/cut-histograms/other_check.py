"""Independent small-group checks of support connectivity and degree lowering."""
from itertools import product
from random import Random
rng=Random(7911)
def verify(mod,p,root,dims,rounds):
    pts=list(product(range(mod),repeat=dims))
    def add(x,y):return tuple((a+b)%mod for a,b in zip(x,y))
    def dot(a,x):return sum(i*j for i,j in zip(a,x))%mod
    def char(a,x):return pow(root,dot(a,x),p)
    ell=2 if mod==4 else mod
    assert pow(root,mod,p)==1 and pow(root,mod//ell,p)!=1
    for _ in range(rounds):
        spec={a:rng.randrange(1,p) for a in rng.sample(pts,rng.randrange(1,min(6,len(pts))+1))}
        table={x:sum(c*char(a,x) for a,c in spec.items())%p for x in pts}
        support={x for x in pts if table[x]}
        anchor=next(iter(spec))
        diffs={tuple((i-j)%mod for i,j in zip(a,anchor)) for a in spec if a!=anchor}
        W={pts[0]}
        while diffs:
            v=max(pts,key=lambda w:sum(dot(a,w)!=0 for a in diffs))
            diffs={a for a in diffs if not dot(a,v)}
            W={add(w,tuple(j*i%mod for i in v)) for w in W for j in range(mod)}
        assert all(any(add(x,w) in support for w in W) for x in pts)
        units=[tuple(int(j==k) for k in range(dims)) for j in range(dims)]
        D=W|{add(w,e) for w in W for e in units}
        seen={next(iter(support))}
        for _ in pts:
            after=seen|{add(x,v) for x in seen for v in D if add(x,v) in support}
            if after==seen:break
            seen=after
        assert seen==support
        a=rng.choice(pts); F=[rng.randrange(ell) for i in range(mod)]
        P={x:F[dot(a,x)] for x in pts}
        for _ in range(mod):
            v=rng.choice(pts); P={x:(P[add(x,v)]-P[x])%ell for x in pts}
        assert not any(P.values())
verify(3,7,2,3,65)
verify(4,5,2,2,65)
print("130 ternary/quaternary support graphs and local iterated-difference checks passed")
