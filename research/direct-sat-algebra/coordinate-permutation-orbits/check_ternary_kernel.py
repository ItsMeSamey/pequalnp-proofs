from random import Random
from ternary_kernel import solve,move,compose,inverse
from itertools import combinations
def check(r,f,p,z,expected_rank=None):
    queue=[p];seen=set(queue)
    for s in queue:
        for t in (r,f):
            x=move(t,s)
            if x not in seen:seen.add(x);queue.append(x)
    status,proof,rank=solve(r,f,p,z,rank_cap=None)
    assert (status=='yes')==any(not v&z for v in seen)
    if expected_rank is not None:assert rank==expected_rank
    if proof:
        ops,h=proof;tab=[tuple(range(len(r))),tuple(r),tuple(f)]
        for row in ops[3:]:tab.append(inverse(tab[row[1]]) if row[0]=='inv' else compose(tab[row[1]],tab[row[2]]))
        assert move(tab[h],p) in seen and not move(tab[h],p)&z
rng=Random(51)
for m in range(1,6):
    for _ in range(25):
        r=[(i+3)%(3*m) for i in range(3*m)];f=list(range(3*m))
        for j in range(m):
            if rng.randrange(4):
                a,b=[3*j+x for x in rng.sample(range(3),2)];f[a],f[b]=f[b],f[a]
        mask=rng.randrange(8);p=sum(mask<<(3*i) for i in range(m));check(r,f,p,rng.randrange(1<<(3*m)))
for m in (2,4,5):
    keys=[(u,v,a) for u,v in combinations(range(m),2) for a in range(3)];r=[];f=[]
    for u,v,a in keys:
        x,y=(u+1)%m,(v+1)%m
        r.append(keys.index((min(x,y),max(x,y),a if x<y else -a%3)))
        f.append(keys.index((u,v,(-a+int(u==0)-int(v==0))%3)))
    p=sum(1<<i for i,(_,_,a) in enumerate(keys) if a==0)
    for _ in range(8):check(r,f,p,p&rng.randrange(1<<len(keys)),m-1)
print('149 exhaustive original orbit and SLP/rank tests')
