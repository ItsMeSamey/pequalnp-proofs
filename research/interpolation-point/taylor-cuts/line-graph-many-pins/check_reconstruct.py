from itertools import combinations
from reconstruct import root_from_graph

def encoded(n,es):
    return sum(1<<i for i,(x,y) in enumerate(combinations(range(n),2)) if set(es[x])&set(es[y]))
def attainable(n):
    masks=set()
    def visit(es,q):
        if len(es)==n:
            masks.add(encoded(n,es))
            return
        for p in combinations(range(q),2):visit(es+[p],q)
        for i in range(q):visit(es+[(i,q)],q+1)
        visit(es+[(q,q+1)],q+2)
    visit([],0)
    return masks
counts=[]
for n in range(6):
    links=list(combinations(range(n),2))
    possible=attainable(n)
    for z in range(1<<len(links)):
        es=[edge for i,edge in enumerate(links) if z>>i&1]
        root=root_from_graph(n,es)
        assert (root is not None)==(z in possible)
        if root is not None:assert encoded(n,root[1])==z
    counts.append((n,len(possible),1<<len(links)))
print(counts)
