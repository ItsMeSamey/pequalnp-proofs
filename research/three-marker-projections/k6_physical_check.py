from itertools import combinations
edges = list(combinations(range(6), 2))
def edge(i,j): return 1 << edges.index(tuple(sorted((i,j))))
K = [edge(i,5)^edge(j,5)^edge(i,j) for i,j in combinations(range(5),2)]
tag = edge(0,1)^edge(2,3)^edge(4,5)
def bit(x): return x.bit_count()%2
def span_basis(values):
    bases = {}
    for x in values:
        while x:
            i = x.bit_length()-1
            if i not in bases:
                bases[i]=x
                break
            x ^= bases[i]
    return list(bases.values())
rels = [x for x in range(1<<15) if all(not bit(x&r) for r in K)]
L=span_basis(x for x in rels if not bit(x&tag))
coords={0:0}
for i,e in enumerate(L):
    coords.update({k^e:v^(1<<i) for k,v in list(coords.items())})
def wedge(u,v):
    return sum((bit((u>>i)&(v>>j)&1)^bit((u>>j)&(v>>i)&1))<<k for k,(i,j) in enumerate(combinations(range(4),2)))
def restricted_rank(q):
    return len(span_basis([sum(bit(q&wedge(1<<i,1<<j))<<j for j in range(4)) for i in range(4)]))
def checks(rows):
    allowed = [x for x in rels if all(not bit(x&r) for r in rows)]
    wedges=set(); maxdim=0; good=0
    for S in range(1<<15):
        active=[x for x in allowed if not x&~S]
        if not rows and any(bit(x&tag) for x in active):continue
        good+=1; maxdim=max(maxdim,len(active).bit_length()-1)
        wedges.update(wedge(coords[x],coords[y]) for x,y in combinations(span_basis(active),2))
    b=span_basis(wedges)
    zero={q for q in range(64) if not any(bit(q&w) for w in b)}
    return good,maxdim,len(b),zero
a=checks([]); b=checks([tag])
assert len(L)==4 and a[1:3]==(2,5) and b[1:3]==(4,6)
assert b[3]=={0} and sorted(restricted_rank(q) for q in a[3])==[0,4]
print(K,tag,a,b)
