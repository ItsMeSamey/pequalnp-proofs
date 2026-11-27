"""Bounded oracle comparison for incidence-toggled line graph certificates."""
from itertools import combinations,product
from random import Random


def xor(xs):
    out=0
    for x in xs:out^=x
    return out


def parity(x):return x.bit_count()%2


def interaction(a,J,b):
    return parity(a&sum(parity(row&b)<<i for i,row in enumerate(J)))


def check(n,E,F,psi,J):
    s=len(J)
    assert all(not(J[i]>>i&1) for i in range(s))
    assert all((J[i]>>j&1)==(J[j]>>i&1) for i,j in combinations(range(s),2))
    labels=[psi[a]^psi[b] for a,b in E]
    adj=[sum(((bool(set(e)&set(f)) and e!=f)^interaction(labels[i],J,labels[j]))<<j
             for j,f in enumerate(E)) for i,e in enumerate(E)]
    raw=set()
    for z in range(1<<len(E)):
        if z&F!=F:continue
        w=xor(b for j,b in enumerate(labels) if z>>j&1)
        deg=[sum(z>>j&1 for j,e in enumerate(E) if v in e)%2 for v in range(n)]
        assert w==xor(p for d,p in zip(deg,psi) if d)
        lam=[d^interaction(p,J,w) for d,p in zip(deg,psi)]
        equal=all(lam[a]==lam[b] for j,(a,b) in enumerate(E) if z>>j&1)
        assert equal==all(not(z>>j&1) or not parity(z&r) for j,r in enumerate(adj))
        if equal:raw.add((w,tuple(lam[v] for v in range(n) if any(v in e and F>>j&1 for j,e in enumerate(E)))))
    forced=[e for j,e in enumerate(E) if F>>j&1]
    named={i for e in forced for i in e}
    rem=[e for j,e in enumerate(E) if not F>>j&1]
    hits=set()
    for mask in range(1<<len(rem)):
        tree=[e for j,e in enumerate(rem) if mask>>j&1]
        vertices=named|{v for e in tree for v in e}
        graph={v:[] for v in vertices}
        for a,b in tree:graph[a].append(b);graph[b].append(a)
        todo=vertices.copy();comps=[]
        while todo:
            root=min(todo);prev={root:None};order=[root]
            for v in order:
                for u in graph[v]:
                    if u not in prev:prev[u]=v;order.append(u)
            todo.difference_update(prev)
            if sum(len(graph[v]) for v in order)!=2*(len(order)-1):break
            if sum(v not in named and len(graph[v])<=1 for v in order)>s+1:break
            comps.append((prev,order))
        else:
            # A singleton unnamed vertex has even beta and contributes zero, so omit.
            if sum(named.isdisjoint(seq) for _,seq in comps)>s:continue
            for w in range(1<<s):
                for colors in product((0,1),repeat=len(comps)):
                    lam={v:c for c,(_,seq) in zip(colors,comps) for v in seq}
                    if any(lam[a]!=lam[b] for a,b in forced):continue
                    beta={v:lam[v]^interaction(psi[v],J,w) for v in lam}
                    if xor(psi[v] for v in lam if beta[v])!=w:continue
                    D=set(forced)
                    for prev,seq in comps:
                        pending={v:beta[v]^(sum(v in e for e in forced)%2) for v in seq}
                        if xor(pending.values()):break
                        for v in reversed(seq[1:]):
                            if pending[v]:
                                u=prev[v];pending[u]^=1;D.add(tuple(sorted((u,v))))
                        assert not pending[seq[0]]
                        # Reconstruct the internal label sum on every path from this root.
                        for v in seq[1:]:
                            path=[v]
                            while prev[path[-1]] is not None:path.append(prev[path[-1]])
                            for alpha in (0,1):
                                nu=[(1|(psi[i]<<1)) if alpha^interaction(psi[i],J,w) else 0 for i in path]
                                for j in range(s+1):
                                    bits=[u>>j&1 for u in nu]
                                    residue=(sum(a+b for a,b in zip(bits,bits[1:]))-bits[0]-bits[-1])%4
                                    assert residue==2*(sum(bits[1:-1])%2)
                    else:
                        z=sum(1<<E.index(e) for e in D)
                        assert z&F==F and all(not(z>>j&1) or not parity(z&r) for j,r in enumerate(adj))
                        hits.add((w,tuple(lam[v] for v in sorted(named))))
    assert hits==raw
    return bool(raw),adj


if __name__=='__main__':
    rng=Random(3928)
    for _ in range(75):
        n=rng.randrange(3,7);s=rng.randrange(4);J=[0]*s
        for i,j in combinations(range(s),2):
            if rng.randrange(2):J[i]|=1<<j;J[j]|=1<<i
        E=sorted(rng.sample(list(combinations(range(n),2)),min(n+1,n*(n-1)//2)))
        F=sum(1<<j for j in rng.sample(range(len(E)),min(3,len(E))))
        check(n,E,F,[rng.randrange(1<<s) for j in range(n)],J)
    E=[(0,1),(2,3),(4,5),(6,7)]
    psi=[0,1,0,2,0,2,0,2]
    assert check(8,E,14,psi,[2,1])==(True,[14,1,1,1])
    assert check(8,E,7,psi,[2,1])==(False,[14,1,1,1])
    print('75 seeded cases matched every (w, named colors); literal claw YES and NO passed')
