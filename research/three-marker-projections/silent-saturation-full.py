from itertools import combinations
from collections import deque

columns=[15,28,21,12,20,14,31,13,4,1]
seeds={1:385,0:578,4:580,3:44,5:416,10:162,6:292,15:176,9:448,8:704,12:832,7:76,11:208,2:104,14:112}
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
assert len(basis)==54 and set(basis.values())==set(range(16))
assert set(seeds)==set(range(16))-{13}
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
    if basis[x]==13:break
    for y in adj[x]:
        if y not in paths:paths[y]=paths[x]+[y];queue.append(y)
print(len(basis),'bases; escaping path',paths[x], 'transfers',[basis[i] for i in paths[x]])
