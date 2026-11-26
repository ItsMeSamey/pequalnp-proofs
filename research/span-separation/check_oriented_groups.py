"""Check signed tree-cotree gains over Z/3 and Z/4 on all edge subsets."""
from itertools import product
from random import Random
from check_auxiliary_graphic import dual_graph

rng=Random(2811)
def forest(n,edges,allowed):
    parent=list(range(n))
    def find(i):
        while i!=parent[i]: i=parent[i]
        return i
    tree=[]
    for j in allowed:
        u,v=edges[j]
        i,k=find(u),find(v)
        if i!=k:
            tree.append(j)
            parent[i]=k
    return tree,[find(i) for i in range(n)]

def check(n,edges,L):
    m=len(edges)
    f,dual=dual_graph(n,edges,rng)
    T,_=forest(n,edges,range(m))
    S,_=forest(f,dual,[j for j in range(m) if j not in T])
    K=[j for j in range(m) if j not in T and j not in S]
    assert len(K)==2-n+m-f and len(S)==f-1
    flow=[rng.randrange(L) for _ in edges]
    labels=[0]*n
    for (u,v),w in zip(edges,flow):
        labels[u]-=w;labels[v]+=w
    null=[]
    for z in product(range(L),repeat=m):
        div=[0]*f
        for j,(a,b) in enumerate(dual):
            div[a]-=z[j];div[b]+=z[j]
        if any(x%L for x in div):continue
        p=[None]*n;p[0]=0
        for _ in range(n):
            for j in T:
                u,v=edges[j]
                if p[u] is not None:p[v]=(p[u]+z[j])%L
                elif p[v] is not None:p[u]=(p[v]-z[j])%L
        if any((z[j]-p[edges[j][1]]+p[edges[j][0]])%L for j in K):continue
        assert all(z[j]==(p[v]-p[u])%L for j,(u,v) in enumerate(edges))
        gain=sum(x*y for x,y in zip(z,flow))%L
        assert gain==sum(x*y for x,y in zip(p,labels))%L
        null.append((sum(1<<j for j,x in enumerate(z) if x),p,gain))
    for X in range(1<<m):
        _,part=forest(n,edges,[j for j in range(m) if not X>>j&1])
        comps=set(part)
        available=[(p,v) for sup,p,v in null if not sup&~X]
        assert len(available)==L**(len(comps)-1)
        roots=[0]+[part.index(c) for c in sorted(comps-{part[0]})]
        for i in range(1,len(roots)):
            hits=[gain for p,gain in available if all(p[w]==int(k==i) for k,w in enumerate(roots))]
            assert hits==[sum(w for w,c in zip(labels,part) if c==part[roots[i]])%L]
    return len(K)//2,1<<m
genera=set();total=0
for _ in range(110):
    n=rng.randint(1,5)
    edges=[(v,rng.randrange(v)) for v in range(1,n)]
    edges += [(rng.randrange(n),rng.randrange(n)) for _ in range(rng.randrange(1,7-len(edges)))]
    g,c=check(n,edges,rng.choice((3,4)))
    genera.add(g);total+=c
print(f"110 signed embeddings, genera {sorted(genera)}, {total} edge subsets")
