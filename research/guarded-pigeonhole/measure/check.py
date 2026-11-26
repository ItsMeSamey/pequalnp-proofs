from itertools import combinations,product
from project import project,mv,dot
from random import Random
rng=Random(720935)
tests=0
for n in range(1,9):
    for _ in range(25):
        A=[0]*n
        for i,j in combinations(range(n),2):
            if rng.randrange(2):
                A[i]|=1<<j; A[j]|=1<<i
        L=[rng.randrange(1<<n) for _ in range(rng.randrange(4))]
        z=rng.randrange(1<<len(L));sites=rng.sample(range(n),min(n,3))
        for choices in product(range(3),repeat=len(sites)):
            result=project(A,L,z,sites,choices)
            affected=[((1<<i,0),(A[i],0),(A[i]^(1<<i),1))[j] for i,j in zip(sites,choices)]
            raw=[x for x in range(1<<n) if mv(L,x)==z and all(dot(x,r)==b for r,b in affected)]
            assert bool(raw)==(result is not None)
            if result:
                B,R,t,lift,transform,_=result
                m=len(B);mask=(1<<m)-1
                actual={transform(x)&mask for x in raw if not (x&mv(A,x))}
                expected={u for u in range(1<<m) if mv(R,u)==t and not(u&mv(B,u))}
                assert actual==expected
                for u in expected:
                    x=lift(u); assert x in raw and not(x&mv(A,x)) and transform(x)&mask==u
            tests+=1
print(tests,'projected branch comparisons passed')
