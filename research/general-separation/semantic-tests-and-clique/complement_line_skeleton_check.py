"""Finite comparison of parity skeletons against direct complement-line supports."""
from itertools import combinations, product
from random import Random
from collections import Counter
import networkx as nx


def valid(D):
    return all(sum(set(e).isdisjoint(f) for f in D)%2==0 for e in D)


def direct(E):
    out={}
    for mask in range(1<<len(E)):
        D=[e for i,e in enumerate(E) if mask>>i&1]
        if valid(D):
            for k in range(min(3,len(D))+1):
                for F in combinations(D,k):out.setdefault(F,set()).add(len(D)%2)
    return out


def branch(E,F,parity,stray=True):
    F=set(F)
    terminals={v for e in F for v in e}
    rem=[e for e in E if e not in F]
    for mask in range(1<<len(rem)):
        chosen=[e for j,e in enumerate(rem) if mask>>j&1]
        V={v for e in chosen for v in e}|terminals
        adj={v:[] for v in V}
        for a,b in chosen:adj[a].append(b);adj[b].append(a)
        todo=V.copy()
        comps=[]
        extra_count=0
        while todo:
            root=min(todo)
            order=[root];prev={root:None};side={root:0}
            for v in order:
                for w in adj[v]:
                    if w not in prev:
                        prev[w]=v;order.append(w);side[w]=side[v]^1
            C=set(order)
            todo-=C
            cotree=[(a,b) for a,b in chosen if a in C and prev[a]!=b and prev[b]!=a]
            if len(cotree)>parity:break
            if cotree and side[cotree[0][0]]!=side[cotree[0][1]]:break
            unnamed=C.isdisjoint(terminals)
            if unnamed:
                extra_count+=1
                if not parity or not stray or extra_count>1:break
                if not(len(C)==2 or (len(C)%2 and all(len(adj[v])==2 for v in C))):break
            if sum(len(adj[v])<=1 for v in C-terminals)>(2 if parity else 1) and not unnamed:break
            comps.append((order,prev,side,cotree,unnamed))
        else:
            for cs in product((0,1),repeat=len(comps)):
                colors={v:(cs[j] if parity else cs[j]^side[v]) for j,(vs,_,side,_,_) in enumerate(comps) for v in vs}
                if any((colors[a]==colors[b])!=bool(parity) for a,b in F):continue
                options=[]
                for vs,prev,side,cotree,unnamed in comps:
                    if unnamed and (len(vs)==2)!=bool(colors[vs[0]]):break
                    demand={v:colors[v]^(sum(v in e for e in F)%2) for v in vs}
                    if sum(demand.values())%2:break
                    solutions=[]
                    for bit in range(1+len(cotree)):
                        rhs=demand.copy();used=[]
                        if bit:
                            a,b=cotree[0];used.append((a,b));rhs[a]^=1;rhs[b]^=1
                        for v in reversed(vs[1:]):
                            if rhs[v]:
                                u=prev[v];rhs[u]^=1;used.append(tuple(sorted((u,v))))
                        assert not rhs[vs[0]]
                        if not cotree:assert len(used)%2==sum(demand[v] for v in vs if side[v])%2
                        solutions.append(used)
                    if cotree:assert len(solutions[0])%2!=len(solutions[1])%2
                    options.append(solutions)
                else:
                    for choices in product(*options):
                        D=F.union(*(set(g) for g in choices))
                        if len(D)%2==parity:
                            assert valid(D)
                            return D
    return None


if __name__=='__main__':
    counts=Counter()
    rng=Random(837)
    for G in nx.graph_atlas_g():
        if len(G)>5:continue
        E=sorted(tuple(sorted(e)) for e in G.edges())
        oracle=direct(E)
        for k in range(min(3,len(E))+1):
            for F in combinations(E,k):
                expected=oracle.get(F,set())
                for par in (0,1):assert (branch(E,F,par) is not None)==(par in expected)
                counts[tuple(sorted(expected))]+=1
    for _ in range(60):
        n=rng.randrange(6,10)
        E=sorted(rng.sample(list(combinations(range(n),2)),rng.randrange(3,10)))
        F=tuple(sorted(rng.sample(E,3)))
        for par in (0,1):assert (branch(E,F,par) is not None)==(par in direct(E).get(F,set()))
    # Two disjoint forced edges are adjacent in the complement line graph.
    # A third disjoint edge makes a triangle and is necessarily an unnamed component.
    F=((0,1),(2,3));E=list(F)+[(4,5)]
    assert branch(E,F,0) is None and branch(E,F,1,False) is None
    assert branch(E,F,1)==set(E)
    # In C6, routes 0-1-2 and 0-5-4-3-2 have unsigned lengths 2 and 0 mod 4.
    # Alternating signed gains orienting every edge even -> odd give 0 on both.
    routes=((0,1,2),(0,5,4,3,2))
    assert [(len(p)-1)%4 for p in routes]==[2,0]
    assert [sum(1 if u%2==0 else -1 for u in p[:-1])%4 for p in routes]==[0,0]
    print('atlas parity types',dict(counts),'and 60 seeded cases passed')
