"""Literal substitution counterexample for the graph 3-coloring blocks."""
from itertools import combinations,product


def verify(n,edges):
    w=1<<(2*n)
    z=[1<<i for i in range(n)]
    t=[1<<(n+i) for i in range(n)]
    blocks=[(z[i],t[i]) for i in range(n)]+[(z[i]^z[j]^w,t[i]^t[j]^w) for i,j in edges]
    ublocks=[1<<(2*n+1+i) for i in range(len(blocks))]
    cols=tuple(q for (l,r),u in zip(blocks,ublocks) for q in (l,l^u,r,r^u))
    phi=w|sum(ublocks[n:])
    witness=sum(1<<(4*i+1) for i in range(len(blocks)))
    degree=[0]*n
    for a,b in edges:
        degree[a]+=1
        degree[b]+=1
    for i,k in enumerate(degree):
        if k%2==0:
            witness|=1<<(4*i)
    total=0
    for i,v in enumerate(cols):
        if witness>>i&1:
            assert (v&phi).bit_count()%2==0
            total^=v
    assert total==sum(ublocks) and (w&phi).bit_count()%2==1


def run():
    tested=bad=0
    for n in range(1,6):
        possible=list(combinations(range(n),2))
        for mask in range(1<<len(possible)):
            edges=[e for i,e in enumerate(possible) if mask>>i&1]
            if len(edges)%2:
                continue
            verify(n,edges)
            ok=any(all(c[a]!=c[b] for a,b in edges) for c in product(range(3),repeat=n))
            tested+=1
            bad+=int(not ok)
    print(tested,"even-edge graphs checked,",bad,"non-three-colorable false positives")


if __name__=="__main__":
    run()
