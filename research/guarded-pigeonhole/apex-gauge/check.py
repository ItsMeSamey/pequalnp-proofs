"""Apex-retaining correction and an exhaustive-oracle small instance test."""
from pathlib import Path
import sys, random
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'fiber-switches'))
from completion import solve,kernel,mv,basis
def transform(n,m,L,s,p,q,retain=True):
    data=[(r,s>>j&1) for j,r in enumerate(L)]
    constraints=[]
    for v in range(n+m):
        cell=data+[(1<<v,1)]; base=solve(cell)
        if base is None:continue
        U=kernel([r for r,_ in cell],n+m)
        for k,w in enumerate([base]+U):
            if v<n:
                row=(w>>n)<<(v*m)
                if k==0 and retain:row^=1<<(n*m+v)
                val=p>>v&1
            else:
                row=sum((w>>i&1)<<(i*m+v-n) for i in range(n))
                val=q>>(v-n)&1
            constraints.append((row,val if k==0 else 0))
    out=solve(constraints)
    if out is None:return None
    return [(out>>(i*m))&((1<<m)-1) for i in range(n)],out>>(n*m)
def profile(C,m,L,p=0,q=0):
    profiles={}
    for x in range(1<<len(C)):
        right=q
        for i,c in enumerate(C):
            if x>>i&1:right^=c
        for y in range(1<<m):
            if x&(mv(C,y)^p) or y&right:continue
            score=mv(L,x|(y<<len(C)))
            profiles.setdefault(score,(x,y))
    return profiles
if __name__=='__main__':
    rng=random.Random(291056);checks=0; strict=None
    for _ in range(6000):
        n=m=3;C=[rng.randrange(8) for _ in range(3)]
        L=list(basis(rng.randrange(64) for _ in range(3)).values())
        if len(L)!=3:continue
        p,q=rng.randrange(1,8),rng.randrange(1,8); s=rng.randrange(8)
        orig=profile(C,m,L,p,q)
        result=transform(n,m,L,s,p,q)
        if result is None:continue
        D,a=result;B=[c^d for c,d in zip(C,D)]
        bare=profile(B,m,L); effect=profile(B,m,L,a,0)
        assert (s in orig)==(s in effect)
        holes=set(range(8))-set(bare)
        if not holes:continue
        h=min(holes);t=h^s
        actual=set(bare)|{v^t for v in effect}
        assert (h in actual)==(s in orig)
        checks+=1
        if s in orig and transform(n,m,L,s,p,q,False) is None and not strict:
            zholes=set(range(8))-set(profile(C,m,L))
            if zholes:strict=(C,L,p,q,s,D,a,h,min(zholes))
    print(checks,'successful hole-forced queries verified;',strict)
