"""Compare induced sink reachability and the two-terminal obstruction on all four-site mixed graphs."""
from itertools import product,combinations
def reaches(v,S,A):
    out={v}
    while True:
        z=out|{j for i in out for j in A[i] if j in S}
        if z==out:return z
        out=z
n=4; vs=set(range(n)); edges=list(combinations(vs,2)); num=0
for code in product(range(4),repeat=len(edges)):
    arcs=[set() for i in vs]; nb=[set() for i in vs]
    for (a,b),val in zip(edges,code):
        if val:
            nb[a].add(b);nb[b].add(a)
        if val&1:arcs[a].add(b)
        if val&2:arcs[b].add(a)
    valid=True
    for m in range(1,1<<n):
        S={i for i in vs if m>>i&1}
        if reaches(min(S),S,nb)==S and not set.intersection(*(reaches(i,S,arcs) for i in S)):valid=False;break
    bad=False
    for u,v in edges:
        if v in nb[u]:continue
        for a,b in product(nb[u]-arcs[u],nb[v]-arcs[v]):
            allowed=vs-{u,v}-(nb[u]-{a})-(nb[v]-{b})
            if a in allowed and b in allowed and b in reaches(a,allowed,nb):bad=True;break
    assert valid!=bad
    num+=valid
print('4096 mixed four-site graphs,',num,'hereditarily common-sink')
