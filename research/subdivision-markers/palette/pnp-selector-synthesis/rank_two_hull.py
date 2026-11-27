"""Least-hull reduction to the one-bit weighted cographic query."""
from itertools import combinations
from collections import deque
from rank_one_grove import query as rank_one_query


def hull(adj,terminals):
    X=set(terminals)
    while True:
        unseen=set(range(len(adj)))-X;forced=None
        while unseen and forced is None:
            root=min(unseen);unseen.remove(root);component=[root];boundary=set()
            for u in component:
                boundary.update(adj[u]&X)
                for v in adj[u]&unseen:
                    unseen.remove(v);component.append(v)
            pair=next(((a,b) for a,b in combinations(sorted(boundary),2) if b not in adj[a]),None)
            if pair:
                a,b=pair;allowed=set(component)|{a,b};todo=deque([a]);pred={a:None}
                while b not in pred:
                    u=todo.popleft()
                    for v in allowed&adj[u]:
                        if v not in pred:pred[v]=u;todo.append(v)
                forced=set();v=b
                while v!=a:forced.add(v);v=pred[v]
        if forced is None:return tuple(sorted(X))
        X.update(forced)


def query(n,edges,omega,trials=1,rng=None):
    edges=tuple(tuple(e) for e in edges);omega=tuple(tuple(p) for p in omega)
    if n<1 or trials<1:raise ValueError("invalid input")
    adj=[set() for _ in range(n)];charge=[0]*n
    for a,b,t in edges:
        if not (0<=a<n and 0<=b<n and 0<=t<4):raise ValueError("invalid edge")
        if a!=b:adj[a].add(b);adj[b].add(a)
        charge[a]^=t;charge[b]^=t
    if any(not 0<=i<j<len(edges) for i,j in omega):raise ValueError("invalid exterior coordinate")
    seen={0};stack=[0]
    for v in stack:
        for u in adj[v]-seen:seen.add(u);stack.append(u)
    if len(seen)!=n:raise ValueError("connected host required")
    if len(set(charge)-{0})<=1:
        got=rank_one_query(n,edges,omega,trials,rng)
        return None if got is None else got[:2]
    candidates=[]
    for lam in (1,2,3):
        T={v for v,q in enumerate(charge) if (q&lam).bit_count()%2}
        X=hull(adj,T);candidates.append((len(X),X,lam,T))
    _,X,lam,T=min(candidates)
    from itertools import product
    for coloring in product(range(3),repeat=len(X)-1):
        colors=dict(zip(X,(0,)+coloring));unseen=set(X);image=list(range(n))
        ok=True
        while unseen:
            root=min(unseen);unseen.remove(root);comp=[root]
            for v in comp:
                for u in adj[v]&unseen:
                    if colors[u]==colors[root]:unseen.remove(u);comp.append(u)
            if len(T.intersection(comp))%2:ok=False;break
            for u in comp:image[u]=root
        if not ok:continue
        verts={v:i for i,v in enumerate(sorted(set(image)))}
        mapped=[(verts[image[a]],verts[image[b]],t) for a,b,t in edges]
        got=rank_one_query(len(verts),mapped,omega,trials,rng)
        if got is not None:return got[:2]
    return None
