from random import Random
from check_relax import test
rng=Random(2405)
total=proper=high=0
for _ in range(360):
    n=rng.randrange(8,15)
    E=[(i,i+1) for i in range(n-1)]+[(0,n-1)]
    deg=[2]*n
    for k in range(rng.randrange(2,n)):
        u,v=sorted((rng.randrange(2),rng.randrange(2,n)))
        if (u,v) not in E and deg[v]<3:
            E.append((u,v))
            deg[u]+=1
            deg[v]+=1
    M=sum(1<<v for v in rng.sample(range(n),rng.randrange(1,6)))
    res=test(E,n,3,M)
    if res is not None:
        total+=1
        proper+=int(res)
        high+=int(min(deg[:2])>3)
print('tested no-spectator cases:',total,'proper K:',proper,'both roots high:',high)
