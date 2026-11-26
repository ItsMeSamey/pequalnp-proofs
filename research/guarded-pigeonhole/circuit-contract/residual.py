"""Check connectivity and signed chordless width on the minimal peeling example."""
from verify import sums
from itertools import combinations
from collections import Counter
A=[264,360,88,7,132,130,134,624,1027,1152,768];L=[1,2,3,4,1,0,5,8,8,0,0];n=len(A)
for rem in range(n):
    seen={int(rem==0)};queue=list(seen)
    for i in queue:
        for j in range(n):
            if j!=rem and A[i]>>j&1 and j not in seen:seen.add(j);queue.append(j)
    assert len(seen)==n-1
sides={0:0};queue=[0]
for i in queue:
    for j in range(n):
        if A[i]>>j&1:
            if j not in sides:sides[j]=1-sides[i];queue.append(j)
            assert sides[i]!=sides[j]
def family(shore):
    side=[i for i in range(n) if sides[i]==shore]
    C={0}
    for i in side:C|={x^(1<<i)^A[i] for x in C}
    circuits=[x for x in C if x and not any(y!=x and y and y&x==y for y in C)]
    chorded={x^y for x,y in combinations(circuits,2) if (x&y).bit_count()==1 and min(x.bit_count(),y.bit_count())>2}
    wt=sums([L[i] if i in side else 0 for i in range(n)])
    return {wt[x] for x in C},[(x,wt[x]) for x in circuits if x not in chorded],C,wt
P,pc,rows,lw=family(0);Q,qc,cols,rw=family(1)
pairs=[(x,y) for x,a in pc for y,b in qc if a not in Q and b not in P and not x&y]
sizes=Counter((x.bit_count(),y.bit_count()) for x,y in pairs)
assert sizes=={(4,4):2,(5,3):4,(5,4):2}
assert all(lw[x]^rw[y]!=6 for x in rows for y in cols if not(x&y))
print('Biconnected; pure images',sorted(P),sorted(Q),'and signed disjoint size profiles',sizes)
from verify import basis
full=(1<<n)-1
for S in range(1,full):
    if min(S.bit_count(),(full^S).bit_count())>=2:
        assert len(basis(A[i]&~S for i in range(n) if S>>i&1))>=2
side=[i for i in range(n) if not sides[i]]
v=[1<<side.index(i) if i in side else sum((A[i]>>j&1)<<k for k,j in enumerate(side)) for i in range(n)]
K=[i for i in range(n) if i not in (0,1,5,7)]
def mr(K):return len(basis([v[0]]+[v[i] for i in K]))-1
assert mr(K)==4 and all(mr([i for i in K if i not in pr])==4 for pr in combinations(K,2))
print('3-connected, F7* minor by contracting 0 and deleting 1,5,7')
