from itertools import product
from random import Random
r=Random(4807); totals=[0,0]
for _ in range(150):
    n=r.randrange(3,7); roots={r.randrange(n)}
    adj=[{j for j in range(n) if j!=i and r.randrange(3)==0} for i in range(n)]
    for par in product(*([i] if i in roots else adj[i] for i in range(n))):
        su={}; bad=False
        for v,w in enumerate(par):
            u=n+v if v in roots else w if w>v else su[w]
            if u==v:bad=True;break
            J={x for x in range(v+1) if any(x in adj[z] for z in range(v+1,n))}
            su={x:(u if x==v or su[x]==v else su[x]) for x in J}
            for x in J:
                z=x; seen=set()
                while z<=v and z not in roots:
                    assert z not in seen
                    seen.add(z);z=par[z]
                assert su[x]==(n+z if z<=v and z in roots else z)
        cyclic=False
        for x in range(n):
            seen=set()
            while x not in roots:
                if x in seen:cyclic=True;break
                seen.add(x);x=par[x]
        assert bad==cyclic
        totals[bad]+=1
print('complete parent maps (acyclic, cyclic):',totals)
assert all(totals)
