"""Exhaust all subsets of the trails in sampled signed witnesses."""
from itertools import combinations
from random import Random
rng=Random(927)
trials=0
for k in range(800):
    n=rng.randrange(2,9); V=set(range(n)); adj=[set() for _ in V]
    for u,v in combinations(V,2):
        if rng.randrange(4)==0:adj[u].add(v);adj[v].add(u)
    S={v for v in V if rng.randrange(2)}
    # Choose an arbitrary witness and derive its necessary biases.
    bias=[len(adj[v]&S)%2 if v in S else rng.randrange(2) for v in V]
    g=[rng.randrange(4) for _ in V]
    I={v for v in S if not adj[v]&S}
    R=V-I-set().union(*(adj[v] for v in I)); S-=I
    H={v for v in R if len(adj[v]&R)>=3-bias[v]}
    T=set()
    for u,v in combinations(sorted(H),2):
        if v in adj[u] and not T&{u,v}:T.add(rng.choice((u,v)))
    U=T&S
    odd={v for v in H-T if (bias[v]+len(adj[v]&U))%2}
    fix=S&H-odd
    E=[(u,v) for u,v in combinations(sorted(S),2) if v in adj[u] and not {u,v}<=H]
    links={};ends={}
    for v in S:
        inc=[i for i,e in enumerate(E) if v in e];rng.shuffle(inc)
        if v in U|odd or v not in H and bias[v]:
            for i in inc:ends[i,v]=v
        else:
            assert len(inc)%2==0
            for x,y in zip(inc[::2],inc[1::2]):links[x,v]=y;links[y,v]=x
    seen=set(); trails=[]
    for i in range(len(E)):
        if i in seen:continue
        comp={i}; stack=[i]
        while stack:
            j=stack.pop()
            for v in E[j]:
                z=links.get((j,v))
                if z is not None and z not in comp:comp.add(z);stack.append(z)
        seen|=comp
        vertices=set().union(*(set(E[j]) for j in comp))
        endpoints=[v for j in comp for v in E[j] if (j,v) in ends]
        assert len(endpoints) in (0,2)
        w=0
        for v in vertices-H:w^=g[v]
        for v in endpoints:
            if v in odd:
                w^=g[v]
                for u in U&adj[v]:w^=1<<(2+u)
            if v in U:w^=1<<(2+v)
        trails.append((vertices,endpoints,w))
    for mask in range(1<<len(trails)):
        active=set(fix);par=set();used=set(); weight=0
        for i,(vert,end,w) in enumerate(trails):
            if mask>>i&1:
                active|=vert;weight^=w
                for v in end:
                    if v in odd:par^={v};used.add(v)
        if par!=used:continue
        for v in active-U:assert len(adj[v]&active)%2==bias[v]
        expect=0
        for v in active-fix:expect^=g[v]
        for v in U:
            if len(adj[v]&(active-fix))%2:expect^=1<<(v+2)
        assert expect==weight
        trials+=1
print(trials,'valid signed trail subfamilies checked')
