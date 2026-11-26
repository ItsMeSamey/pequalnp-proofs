"""Raw native guards, arbitrary simultaneous core/auxiliary zero-deletions, shared witnesses."""
from itertools import combinations
from functools import reduce,lru_cache
G=[56,32,24,5,5,3]
L=[0,5,0,0,7,6]
n=len(G)
def feas(A,x):return all(not(x>>i&1) or not((row&x).bit_count()%2) for i,row in enumerate(A))
def score(x):return reduce(int.__xor__,[l for i,l in enumerate(L) if x>>i&1],0)
def graph(N):
    A=G.copy()+[0]*4
    def edge(i,j):A[i]|=1<<j;A[j]|=1<<i
    for i in range(n):
        if N>>i&1:edge(i,n+int(i>=3))
    edge(n,n+2);edge(n+2,n+3);edge(n+3,n+1)
    return A
planes={sum(1<<i for i in [a,b,c,a^b^c]) for a,b,c in combinations(range(32),3)}
assert len(planes)==1240
@lru_cache(None)
def empty_union(J):return reduce(int.__or__,(p for p in planes if not p&J),0)
def down(rows):
    out=[0]*(1<<(n+4))
    for x in rows:out[x]=1<<(score(x)+8*((x>>n)&3))
    for i in range(n+4):
        for a in range(1<<(n+4)):
            if a>>i&1:out[a]|=out[a^(1<<i)]
    return out
native=[]
for N in (3,11):
    A=graph(N)
    S={x for x in range(1<<(n+4)) if feas(A,x)}
    native.append(S)
    O=[r|((N>>i&1)<<n) for i,r in enumerate(G)]+[N]
    models=[x for x in range(1<<(n+1)) if feas(O,x) and (score(x)^(7 if x>>n&1 else 0))==3]
    print('hood',N,'original witnesses',models)
j0,j1,common=map(down,[native[0],native[1],native[0]&native[1]])
diff=[];shared=[]
for t in range(len(j0)):
    if empty_union(j0[t])!=empty_union(j1[t]):diff.append(t)
    if empty_union(j0[t])!=empty_union(common[t]) or empty_union(j1[t])!=empty_union(common[t]):shared.append(t)
core=lambda t:t>>n==15
print('core-deletion distinguishing subsets',list(filter(core,diff))[:10],sum(map(core,diff)))
print('auxiliary+core deletion distinguishing subsets',len(diff),'first',diff[:5])
print('core-deletion subsets lacking common witness on some query',sum(map(core,shared)),list(filter(core,shared))[:5])
print('all masks lacking common witness on some query',len(shared))
assert not any(map(core,diff))
assert not diff and not shared
for i in range(2):
    exclusive=native[i]-native[1-i]
    hard=[]
    for x in exclusive:
        q=score(x)+8*((x>>n)&3)
        if not (common[x]>>q&1):hard.append((x,q,common[x]))
    print('side',i,'total, exclusive, hard',len(native[i]),len(exclusive),len(hard))
    print('hard',hard)
