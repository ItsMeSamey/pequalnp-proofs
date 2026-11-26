from itertools import combinations
from random import Random
def par(x):return x.bit_count()%2
def scores(cols,x):
    out=0
    for i,v in enumerate(cols):
        if x>>i&1:out^=v
    return out
def span(vs):
    a={0}
    for v in vs:a|={w^v for w in a}
    return a
r=Random(7551);checks=paths=active=0
for it in range(120):
    n=r.randrange(3,7);E=list(combinations(range(n),2));r.shuffle(E);E=E[:min(len(E),8)]
    h=r.choice((1,2));p=r.choice((1,2));q=2
    W=[r.randrange(1<<q) for _ in range(n)];H=[r.randrange(1<<h) for _ in range(n)]
    K={r.randrange(n)};gamma=[H[a]^H[b]^(r.randrange(1<<h) if a in K or b in K else 0) for a,b in E]
    ell=[r.randrange(1<<p) for _ in E]
    for kap in range(1<<h):
        switch=sum(par(kap&v)<<i for i,v in enumerate(H));delta=scores(W,switch)
        native=set();pattern=set()
        for S in range(1<<len(E)):
            es=[(a,b) for i,(a,b) in enumerate(E) if S>>i&1]
            adj=[set() for _ in range(n)]
            for a,b in es:adj[a].add(b);adj[b].add(a)
            if any(len(f)%2 for f in adj) or scores(gamma,S):continue
            core={i for i,f in enumerate(adj) if f}; targetP=scores(ell,S)
            parts=[];rest=set(core)
            while rest:
                todo=[rest.pop()]
                for a in todo:
                    for b in adj[a]:
                        if b in rest:rest.remove(b);todo.append(b)
                parts.append(todo)
            fixed=set(K)&core
            for a,b in es:
                if a in K or b in K:fixed.update((a,b))
            fixed.update(i for i in core if len(adj[i])!=2)
            for comp in parts:
                if not fixed.intersection(comp):fixed.add(comp[0])
            segs=[];used=set()
            for a in fixed:
                for b in adj[a]:
                    if frozenset((a,b)) in used:continue
                    trail=[a,b];used.add(frozenset((a,b)))
                    while trail[-1] not in fixed:
                        c=next(v for v in adj[trail[-1]] if v!=trail[-2]);used.add(frozenset((trail[-1],c)));trail.append(c)
                    segs.append(trail)
            assert len(used)==len(es)
            for x in range(1<<n):
                if any(((x>>a)^(x>>b)^par(kap&gamma[i]))&1 for i,(a,b) in enumerate(E) if S>>i&1):continue
                native.add((targetP,scores(W,x)))
                if len(es)-len(core)+len(parts)>p+h:continue
                y=x^switch;active+=1
                moment=delta^scores(W,sum(1<<v for v in fixed if y>>v&1))
                for t in segs:
                    if len(t)<=2:continue
                    assert len({y>>v&1 for v in t})==1
                    if not(y>>t[0]&1):continue
                    for bit in range(q):
                        val=sum((W[a]>>bit&1)+(W[b]>>bit&1) for a,b in zip(t,t[1:]))-(W[t[0]]>>bit&1)-(W[t[-1]]>>bit&1)
                        moment^=(val%4//2)<<bit
                    paths+=1
                for extra in span(W[i] for i in set(range(n))-core):
                    pattern.add((targetP,moment^extra))
        assert pattern==native
        checks+=1
print(checks,'exact mixed image checks;',active,'colored supports;',paths,'weighted monochrome segment checks')
