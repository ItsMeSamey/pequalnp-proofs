from check import *
from itertools import chain
rng=random.Random(19390)
for it in range(200000):
    n=m=3;C=[rng.randrange(1,8) for _ in range(3)]
    if ((C[0]|C[1]|C[2])!=7 or any(not any(C[i]&C[j] for j in range(3) if j!=i) for i in range(3))):continue
    L=list(basis(rng.randrange(64) for _ in range(3)).values())
    if len(L)!=3:continue
    p,q=rng.randrange(1,8),rng.randrange(1,8)
    if p.bit_count()+q.bit_count()<4:continue
    s=rng.randrange(1,8)
    if s not in profile(C,m,L,p,q) or transform(n,m,L,s,p,q,False):continue
    out=transform(n,m,L,s,p,q)
    if out is None:continue
    D,a=out
    if not any(D):continue
    B=[c^d for c,d in zip(C,D)]
    holes=set(range(8))-set(profile(B,m,L));oh=set(range(8))-set(profile(C,m,L))
    if holes and oh:
        print(it,C,L,p,q,s,D,a,min(holes),min(oh));break
