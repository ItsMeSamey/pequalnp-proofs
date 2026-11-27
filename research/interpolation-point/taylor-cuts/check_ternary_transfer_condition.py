"""Ground comparisons of both conditioning modes and original colour witnesses."""
from itertools import combinations, product
from random import Random
from ternary_transfer_condition import full_support
from ternary_frame import color

rng=Random(86442)
for _ in range(240):
    n=rng.randrange(8)
    r=rng.randrange(6)
    cols={3*j+1:tuple(rng.randrange(3) for i in range(r)) for j in range(n)}
    feasible=any(all(sum(s*v[i] for s,v in zip(signs,cols.values()))%3==0 for i in range(r))
                 for signs in product((1,2),repeat=n))
    interface=rng.sample(list(cols),rng.randrange(min(3,n)+1))
    for mode in ("pin","contract"):
        status,model,_=full_support(cols,supplied=interface,modes=(mode,))
        assert (status=="SAT")==feasible and status!="UNKNOWN"
        if model is not None:
            assert set(model)==set(cols) and set(model.values())<={1,2}
            assert all(sum(model[x]*v[i] for x,v in cols.items())%3==0 for i in range(r))
for _ in range(100):
    n=rng.randrange(1,8)
    edges=[e for e in combinations(range(n),2) if rng.randrange(3)]
    feasible=any(all(a[i]!=a[j] for i,j in edges) for a in product(range(3),repeat=n))
    status,colors,_=color(n,edges,transfer_rank=1,use_prism=rng.choice((True,False)))
    assert (status=="SAT")==feasible
    assert not feasible or all(colors[i]!=colors[j] for i,j in edges)

r=15
def unit(i):
    return tuple(int(k==i) for k in range(r+1))
cols={0:unit(0)}
for i in range(1,r+1):
    cols[2*i-1]=unit(i)
    cols[2*i]=tuple((x+y)%3 for x,y in zip(unit(0),unit(i)))
status,_,s=full_support(cols,supplied=[0],cap=3,modes=("contract",))
assert status=="SAT" and s['transfer_blocks']==r+1 and s['transfer_bound']==3

k=9
edges=[(3*j+a,3*j+b) for j in range(k) for a,b in combinations(range(3),2)]
edges.extend((i,3*j+i) for j in range(1,k) for i in range(3))
assert color(3*k,edges,cap=8)[0]=="UNKNOWN"
status,colors,stats=color(3*k,edges,transfer_rank=1,cap=8)
assert status=="SAT" and all(colors[a]!=colors[b] for a,b in edges)
assert stats['transfer_mode']=="pin" and stats['transfer_bound']==8
print("480 matrix mode comparisons, 100 source graphs, rank-16 contraction and 27-vertex prism hub passed")
