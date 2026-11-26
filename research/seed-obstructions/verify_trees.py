import sys
from pathlib import Path
from itertools import combinations
base=Path(__file__).resolve().parent
sys.path.insert(0,str(base))
from verify_packing import samples
raw,front,target=samples(base/'L-meta-18968.json')
def cv(r):
    p=r&8191
    return ((r>>13)&127)|sum((any(p>>((6+j+d)%13)&1 for d in [0,1,3,9]))<<(7+j) for j in range(7))
ps=sorted({cv(r) for i,r in enumerate(raw) if ((target^front)>>i)&1})
ns=sorted({cv(r) for i,r in enumerate(raw) if not ((target>>i)&1)})
# Coordinates separating each positive/negative pair are independent obligations.
pairs=[(p,n) for p in ps for n in ns]
def mask(test):
    return sum(1<<i for i,(p,n) in enumerate(pairs) if test(p,n))
ALL=(1<<len(pairs))-1
P=[mask(lambda p,n,j=j:p>>j&1) for j in range(14)]
N=[mask(lambda p,n,j=j:n>>j&1) for j in range(14)]
# Quotient by associativity and commutativity. Each node is interned as its
# sorted maximal same-operation children.
nodes=[('leaf',(i,)) for i in range(14)]
ids={n:i for i,n in enumerate(nodes)}
def merge(i,j,op):
    parts=[]
    for k in (i,j):
        name,kids=nodes[k]
        parts.extend(kids if name==op else [k])
    node=(op,tuple(sorted(parts)))
    if node not in ids:
        ids[node]=len(nodes);nodes.append(node)
        P.append(P[i]&P[j] if op=='and' else P[i]|P[j])
        N.append(N[i]&N[j] if op=='and' else N[i]|N[j])
    return ids[node]
levels={tuple(range(14))}
for t in range(13):
    nxt=set()
    for s in levels:
        for i,j in combinations(s,2):
            rest=tuple(k for k in s if k!=i and k!=j)
            uncovered=ALL
            for k in rest:uncovered&=~(P[k]&~N[k])
            for op in ['and','or']:
                pos=P[i]&P[j] if op=='and' else P[i]|P[j]
                neg=N[i]&N[j] if op=='and' else N[i]|N[j]
                if uncovered&(~pos|neg):continue
                h=merge(i,j,op)
                nxt.add(tuple(sorted((*rest,h))))
    levels=nxt
    print(t+1,len(nxt),flush=True)
def display(k):
    name,kids=nodes[k]
    return (('L' if k<7 else 'P')+str(k%7+6)) if name=='leaf' else (name,*(display(i) for i in kids))
for (k,) in sorted(levels):print(display(k))
expected=('or',*(('and',f'L{j}',f'P{j}') for j in range(6,13)))
assert len(levels)==1
def normalized(k):
    op,kids=nodes[k]
    if op=='leaf':return display(k)
    return (op,*sorted(normalized(i) for i in kids))
root=next(iter(levels))[0]
assert normalized(root)==('or',*sorted(expected[1:]))
