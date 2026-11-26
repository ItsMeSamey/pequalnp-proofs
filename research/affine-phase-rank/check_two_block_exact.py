"""Independent rational coefficient enumeration and six-bit geometry crosschecks."""
from itertools import combinations,product
from fractions import Fraction as F
def basis_solution(rows):
    M=[list(map(F,row))+[F(1)] for row in rows]
    for j in range(3):
        k=next((k for k in range(j,3) if M[k][j]),None)
        if k is None: return None
        M[j],M[k]=M[k],M[j]
        pivot=M[j][j]
        M[j]=[x/pivot for x in M[j]]
        for k in range(3):
            if k==j: continue
            c=M[k][j]
            M[k]=[a-c*b for a,b in zip(M[k],M[j])]
    c=tuple(sorted(abs(row[-1]) for row in M))
    return c if all(c) else None
def profiles(values):
    return {c for rows in combinations(product(values,repeat=3),3) if (c:=basis_solution(rows))}
pats=profiles((-1,0,1))
raw="1/3 2/3 2/3;1/3 2/3 4/3;1/2 1/2 1/2;1/2 1/2 1;1/2 1/2 3/2;1/2 1 3/2;1 1 1;1 1 2;1 1 3;1 2 2;1 2 3;1 2 4;2 2 3;2 3 4"
assert pats=={tuple(map(F,item.split())) for item in raw.split(';')}
assert profiles((-1,1))=={(1,1,1)}
def subspaces(d):
    for piv in combinations(range(6),d):
        slots=[(i,k) for i,j in enumerate(piv) for k in range(j+1,6) if k not in piv]
        for m in range(1<<len(slots)):
            B=[1<<j for j in piv]
            for h,(i,k) in enumerate(slots):
                if m>>h&1:B[i]|=1<<k
            X=[0]
            for u in B:X+=[v^u for v in X]
            yield B,X
def cubic(x):return int(x&7==7)^int(x>>3==7)
def mob(v):
    v=v[:]
    for j in range(len(v).bit_length()-1):
        for i in range(len(v)):
            if i>>j&1:v[i]^=v[i^(1<<j)]
    return v
for b,xs in subspaces(5):
    assert any(z and i.bit_count()==3 for i,z in enumerate(mob([cubic(x) for x in xs])))
# Check all 1395 possible direction triples D in the (1,1,2) argument directly:
# If T vanishes on W, T+D cannot vanish on a hyperplane.
def signature(vs,fn):
    V=[0]
    for w in vs: V+=[v^w for v in V]
    return sum(fn(v) for v in V)%2
triples=list(combinations(range(6),3))
def sig(fn):
    return tuple(signature([1<<i for i in t],fn) for t in triples)
T=sig(cubic)
hyper=list(subspaces(5))
# Hyperplane restriction map acts linearly on input's 20 cubic coordinates.
def word(bits):return sum(v<<i for i,v in enumerate(bits))
hmasks=[]
for b,_ in hyper:
    tests=[]
    for triple in combinations(b,3):
        tests.append(word([signature(triple,lambda x,mask=sum(1<<i for i in t):int(x&mask==mask)) for t in triples]))
    hmasks.append(tests)
checked=0
for b,xs in subspaces(3):
    if signature(b,cubic):continue
    support=set(xs)
    D=sig(lambda v:int(v in support))
    M=word([a^c for a,c in zip(T,D)])
    assert all(any((M&mask).bit_count()%2 for mask in tests) for tests in hmasks)
    checked+=1
print("All 14 coefficient patterns and all 63 hyperplanes verified;",checked,"quadratic 3-space directions exclude the (1,1,2) escape")
