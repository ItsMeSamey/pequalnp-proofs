from itertools import combinations
from collections import deque

columns=[4,3,25,15,31,28,21,29,6,13]
seeds={0:146,1:769,2:552,3:524,5:266,7:44,8:168,9:392,10:138,11:532,12:416,13:296,14:800,15:262}
def span(columns):
    v={0}
    for x in columns:v|={a^x for a in v}
    return v
N={x%8 for x in columns}
assert span(N)==set(range(8))
for k in range(1,len(N)):
    for c in combinations(N,k):
        assert len(span(c))*len(span(N-set(c)))>8
basis={}
for ix in combinations(range(len(columns)),3):
    L=span([columns[i] for i in ix])
    if {x%8 for x in L}!=set(range(8)):continue
    a,=[x//8 for x in L if x%8==1];b,=[x//8 for x in L if x%8==2]
    basis[sum(1<<i for i in ix)]=a+4*b
assert len(basis)==67 and set(basis.values())==set(range(16))-{4}
assert set(seeds)==set(range(16))-{4,6}
adj={i:[j for j in basis if (i^j).bit_count()==2] for i in basis}
for t,start in seeds.items():
    assert basis[start]==t
    q=[start]; seen={start}
    for i in q:
        for j in adj[i]:
            assert basis[j] in seeds
            if basis[j]==t and j not in seen:q.append(j);seen.add(j)
paths={x:[x] for x in seeds.values()}; queue=deque(paths)
while queue:
    x=queue.popleft()
    if basis[x]==6:break
    for y in adj[x]:
        if y not in paths:paths[y]=paths[x]+[y];queue.append(y)
print(len(basis),'bases; escaping path',paths[x], 'transfers',[basis[i] for i in paths[x]])
