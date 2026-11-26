"""A five-gate physical one-tour word with a nonlineable shifted paired pencil."""
from itertools import product,combinations
from single_cycle_check import orbits,rank

word='vcdvabvbabadcdc'
names='vabcd'
points={g:[j for j,v in enumerate(word) if v==g] for g in names}
base=list(range(1,len(word)))+[0]
def shift(p,cycle):
    out=p.copy()
    for a,b in zip(cycle,cycle[1:]+cycle[:1]):out[a]=p[b]
    return out
gates=[]
for name in names:
    t=points[name];good=[t1 for t1 in (t,t[::-1]) if len(orbits(shift(base,t1))[1])==1]
    assert len(good)==1
    gates.append(good[0])
for mask in range(32):
    p=base
    for j,triple in enumerate(gates):
        if mask>>j&1:p=shift(p,triple)
    assert len(orbits(p)[1])==1

def blocks(x,y):
    a,b=points[x],points[y]
    return [sum(int((a[0]<b[0]<a[j])^(a[0]<b[k]<a[j]))<<(k-1) for k in (1,2)) for j in (1,2)]
C=[0]*10;edges={}
for i,j in combinations(range(5),2):
    x,y=names[i],names[j]
    R=blocks(x,y)
    if not any(R):continue
    assert rank(R)==1
    factors=(int(bool(R[0]))+2*int(bool(R[1])),next(v for v in R if v))
    edges[x+y]=factors
    for a,b in product(range(2),repeat=2):
        if R[a]>>b&1:C[2*i+a]|=1<<(2*j+b);C[2*j+b]|=1<<(2*i+a)
assert set(edges)=={'va','vb','vc','vd','ab','cd'}
for mask in range(1,32):
    S=sum(3<<(2*i) for i in range(5) if mask>>i&1)
    assert rank([C[i]&S for i in range(10) if S>>i&1])<S.bit_count()
# An unused fourth label also covers lines not orthogonal to any of the
# binary endpoint factors, so this rules out extension-field lines as well.
for L in product(range(1,5),repeat=5):
    assert any(L[names.index(x)]!=u and L[names.index(y)]!=v
               for (x,y),(u,v) in edges.items())
print(word,'gates',gates,'types',edges,'rows',C)
print('32 one-tour masks, 31 singular nonempty paired minors, no incidence-color cover')
