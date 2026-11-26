from random import Random
from solve import solve
rng=Random(1608);positive=0;negative=0
for _ in range(85):
    n=rng.randrange(0,5);d=rng.randrange(0,3);t=rng.randrange(1,4)
    word=list(range(n))*2;rng.shuffle(word)
    pos=[[k for k,u in enumerate(word) if u==i] for i in range(n)]
    A=[sum(1<<j for j,(c,d1) in enumerate(pos) if (a<c<b)^(a<d1<b)) for a,b in pos]
    AC=[rng.randrange(1<<n) for j in range(d)]
    AA=[0]*d
    for j in range(d):
        for k in range(j):
            if rng.randrange(2):AA[j]|=1<<k;AA[k]|=1<<j
    full=[v|sum(((AC[j]>>i)&1)<<(n+j) for j in range(d)) for i,v in enumerate(A)]
    full.extend(AC[j]|(AA[j]<<n) for j in range(d))
    L=[rng.randrange(1<<t) for i in full];z=rng.randrange(1<<t)
    yes=set()
    for x in range(1<<len(full)):
        w=0
        for i,row in enumerate(full):
            if x>>i&1:
                if (x&row).bit_count()%2:break
                w^=L[i]
        else:
            if w==z:yes.add(x)
    result=solve(word,L[:n],L[n:],AC,AA,t,z,rng,repetitions=6)
    assert (result is not None)==bool(yes)
    if result is not None:
        assert result[0]|(result[1]<<n) in yes
        positive+=1
    else:negative+=1
print('Pfaffian solver vs native oracle:',positive,'positive witnesses and',negative,'NO inputs')
