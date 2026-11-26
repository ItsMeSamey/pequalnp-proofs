from itertools import combinations,product
from random import Random
from six_regular_girth_sdp_check import girth
from stable_oct_colour import reference_colouring,stable_oct_colour,_bipartite_or_cycle


def w35():
    def canon(v):
        s=pow(next(i for i in v if i),-1,5)
        return tuple(t*s%5 for t in v)
    pts=[v for v in product(range(5),repeat=4) if any(v) and next(i for i in v if i)==1]
    ids={v:i for i,v in enumerate(pts)}
    lines=set()
    for u,v in combinations(pts,2):
        if (u[0]*v[1]-u[1]*v[0]+u[2]*v[3]-u[3]*v[2])%5==0:
            line=[ids[u]]
            for c in range(5):
                line.append(ids[canon([(a*c+b)%5 for a,b in zip(u,v)])])
            lines.add(tuple(sorted(line)))
    adj=[set() for _ in range(len(pts)+len(lines))]
    for i,line in enumerate(sorted(lines),len(pts)):
        for j in line:adj[i].add(j);adj[j].add(i)
    return adj,len(pts)


def valid(adj,c):
    return c is not None and all(c[u]!=c[v] for u,neigh in enumerate(adj) for v in neigh)


if __name__=='__main__':
    rng=Random(787)
    for _ in range(80):
        n=rng.randrange(1,8);adj=[set() for i in range(n)]
        for u,v in combinations(range(n),2):
            if rng.randrange(3)==0:adj[u].add(v);adj[v].add(u)
        h=[rng.randrange(2) for i in range(n)];k=rng.randrange(n+1)
        F={i for i in range(n) if rng.randrange(9)==0};E={i for i in range(n) if rng.randrange(9)==0}
        colourings=[s for s in product(range(3),repeat=n) if valid(adj,s) and all(s[i]==2 for i in F) and all(s[i]!=2 for i in E)]
        r=reference_colouring(adj,h,chosen=F,excluded=E)
        assert (r is not None)==any(all(c==2 or c==h[i] for i,c in enumerate(s)) for s in colourings)
        o=stable_oct_colour(adj,k,chosen=F,excluded=E)
        assert (o is not None)==any(s.count(2)<=k for s in colourings)
        if o is not None: assert o in colourings and o.count(2)<=k
        if r is not None: assert r in colourings
    adj,split=w35()
    assert len(adj)==312 and split==156 and girth(adj)==8
    a=0;b=min(adj[a]);c=min(adj[b]-{a});d=min(adj[c]-{b})
    for u,v in ((a,b),(c,d)):adj[u].remove(v);adj[v].remove(u)
    for u,v in ((a,c),(b,d)):adj[u].add(v);adj[v].add(u)
    g=girth(adj)
    assert g==7 and all(len(v)==6 for v in adj)
    col=reference_colouring(adj,[int(i>=split) for i in range(len(adj))],chosen=(a,d),excluded=(b,c))
    assert valid(adj,col)
    _,odd1=_bipartite_or_cycle(adj,set())
    _,odd2=_bipartite_or_cycle(adj,set(odd1))
    assert odd2 and set(odd1).isdisjoint(odd2) and len(odd1)%2==len(odd2)%2==1
    assert all(c[(i+1)%len(c)] in adj[v] for c in (odd1,odd2) for i,v in enumerate(c))
    assert stable_oct_colour(adj,0) is None and stable_oct_colour(adj,1) is None
    w=stable_oct_colour(adj,2)
    assert valid(adj,w) and w.count(2)==2
    print('80 constrained graph checks against brute force; switched W(3,5): 312 vertices, 936 edges, regular degree 6, girth 7, stable OCT exactly 2')
