"""Small CSS recognizer checked independently against graph local-complementation orbits."""
from itertools import combinations
from collections import Counter
import networkx as nx
from hidden_cubic_counter import _linear


def mul(A,x):
    return sum(((r&x).bit_count()%2)<<i for i,r in enumerate(A))


def projectors(A):
    n=len(A)
    equations=[]
    def bit(i,j):return 1<<(4*i+j)
    for i in range(n):
        equations.append((bit(i,0)^bit(i,3),1))
        for j in range(n):
            mask=bit(i,2) if i==j else 0
            if A[i]>>j&1:mask^=bit(i,3)^bit(j,0)
            for k in range(n):
                if A[i]>>k&A[k]>>j&1:mask^=bit(k,1)
            equations.append((mask,0))
    sol=_linear(equations,4*n)
    if sol is None:return None
    origin,directions=sol
    for size in range(3):
        for choices in combinations(directions,size):
            w=origin
            for v in choices:w^=v
            blocks=[(w>>(4*i))&15 for i in range(n)]
            det=[((b&(b>>3))^((b>>1)&(b>>2)))&1 for b in blocks]
            assert len(set(det))<=1
            if not any(det):return blocks
    return None


def transform_test(A,blocks):
    n=len(A)
    F=(1<<n)-1
    maps=[]
    for b in blocks:
        def proj(x):
            u,v=x&1,x>>1
            return ((b&u)^((b>>1)&v))&1 | ((((b>>2)&u)^((b>>3)&v))&1)<<1
        im=next(x for x in range(1,4) if proj(x)==x)
        ker=next(x for x in range(1,4) if proj(x)==0)
        table={0:0,im:1,ker:2,im^ker:3}
        assert set(table.values())==set(range(4))
        maps.append(table)
    L=set();aff=set();good=0
    for x in range(1<<n):
        y=mul(A,x)
        z=[(x>>i&1)|((y>>i&1)<<1) for i in range(n)]
        def pack(v):
            return tuple(sum(((a>>j)&1)<<i for i,a in enumerate(v)) for j in range(2))
        lin=[g[v] for g,v in zip(maps,z)]
        h=[3^g[v^3] for g,v in zip(maps,z)]
        L.add(pack(lin));aff.add(pack(h))
        assert (3 not in z)==(3 not in h)
        for i,g in enumerate(maps):assert (z[i]==1)==(h[i]==(3^g[2]))
        good+=3 not in z
    D={x for x,y in L}
    perp={y for y in range(1<<n) if all(not((y&x).bit_count()%2) for x in D)}
    assert L=={(x,y) for x in D for y in perp}
    u,v=pack([3^g[3] for g in maps])
    assert aff=={(x^u,y^v) for x,y in L}
    assert good==sum(not(x&y) for x,y in aff)


def orbit_bipartite(A,cache):
    A=tuple(A)
    if A in cache:return cache[A]
    stack=[A];seen={A};positive=False
    while stack:
        B=stack.pop()
        if not positive:
            g=nx.Graph()
            g.add_nodes_from(range(len(B)))
            g.add_edges_from((i,j) for i in range(len(B)) for j in range(i) if B[i]>>j&1)
            positive=nx.is_bipartite(g)
        for u,row in enumerate(B):
            C=tuple(r^(row&~(1<<i)) if row>>i&1 else r for i,r in enumerate(B))
            if C not in seen:
                seen.add(C);stack.append(C)
    cache.update(dict.fromkeys(seen,positive))
    return positive


if __name__=='__main__':
    cache={}
    hist=Counter()
    for G in nx.graph_atlas_g():
        n=len(G)
        if n>6:continue
        A=[sum(1<<j for j in G[i]) for i in range(n)]
        blocks=[0]*n
        for comp in nx.connected_components(G):
            ids=sorted(comp)
            sub=[sum(1<<k for k,j in enumerate(ids) if j in G[i]) for i in ids]
            part=projectors(sub)
            if part is None:
                blocks=None
                break
            for i,b in zip(ids,part):blocks[i]=b
        assert (blocks is not None)==orbit_bipartite(A,cache)
        if blocks is not None:transform_test(A,blocks)
        hist[n,blocks is not None]+=1
    assert projectors([(1<<((i+1)%5))|(1<<((i-1)%5)) for i in range(5)]) is None
    print('atlas accepted/rejected',sorted(hist.items()))
