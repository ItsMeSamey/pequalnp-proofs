"""Differential oracle using only original bipartite perfect matchings."""
from itertools import product
from random import Random
from ternary_portal_routes import solve


def trial(n, extras, portals, base_weights=None, relabel=None):
    base_weights = [0]*n if base_weights is None else base_weights
    graph = [(i,n+i,(base_weights[i],)) for i in range(n)]
    graph.extend((i,n+j,((g+base_weights[i])%3,)) for i,j,g in extras)
    if relabel is not None:
        graph = [(relabel[b],relabel[a],w) if j%2 else (relabel[a],relabel[b],w)
                 for j,(a,b,w) in enumerate(graph)]
    base = tuple(range(n))
    allowed = set()
    def extend(v, seen, picks, total):
        if v == n:
            allowed.add((total%3, tuple(sorted(picks))))
            return
        left = relabel[v] if relabel is not None else v
        for j,(a,b,w) in enumerate(graph):
            if left not in (a,b):
                continue
            right = b if left == a else a
            if right not in seen:
                extend(v+1, seen|{right}, picks+[j], total+w[0])
    extend(0,set(),[],0)
    tested=0
    for t in range(3):
        for kwargs in ({}, {"portals":portals}):
            stat, ids, _ = solve(2*n,graph,base,(t,),**kwargs)
            if any(g==t for g,_ in allowed):
                assert stat=="SAT" and (t,tuple(sorted(ids))) in allowed, (n,extras,kwargs,t,stat,ids)
            else:
                assert stat=="UNSAT", (n,extras,kwargs,t,stat)
            tested+=1
    return tested


def main():
    tests=0
    # Independent direct graph oracle checks all digon label combinations, plus loops.
    for a,b,c in product((None,0,1,2),repeat=3):
        es=[(i,j,w) for i,j,w in ((0,1,a),(1,0,b),(0,0,c)) if w is not None]
        tests+=trial(2,es,[0])
    # A pair of wrong-gain cycles is the only way to attain the target.
    tests+=trial(4,[(0,1,1),(1,0,1),(2,3,2),(3,2,0)],[0,2])
    # Each external boundary arrival is also a departure; paths of length zero coexist.
    tests+=trial(6,[(0,2,1),(2,1,0),(1,3,1),(3,0,0),(2,3,0),(3,2,0)], [0,1])
    # Both routes traverse the same neutral SCC; free permutation of their endpoints.
    tests+=trial(6,[(0,2,1),(1,3,1),(4,0,0),(5,1,0),
                    (2,5,2),(5,3,2),(3,4,1),(4,2,1)], [0,1])
    # Distinct parallel arcs, disconnected SCCs, nonzero base, unused isolated pair.
    tests+=trial(5,[(0,1,1),(0,1,2),(1,0,0),(2,2,2),(3,3,0)], [0,2], [1,2,1,1,0])
    # Outside portals, within-block gains telescope and interblock arcs point forward.
    rng=Random(628106)
    for _ in range(100):
        n=rng.randrange(2,7)
        portals=rng.sample(range(n),rng.randrange(min(3,n)+1))
        block=[rng.randrange(3) for i in range(n)]
        phi=[rng.randrange(3) for i in range(n)]
        weights=[rng.randrange(3) for i in range(n)]
        edges=[]
        for i,j in product(range(n),repeat=2):
            free=i in portals or j in portals
            if not free and block[i]>block[j]:
                continue
            for _ in range(1+(rng.randrange(12)==0)):
                if rng.randrange(4)==0:
                    g=rng.randrange(3) if free or block[i]<block[j] else (phi[j]-phi[i])%3
                    edges.append((i,j,g))
        labels=list(range(2*n))
        rng.shuffle(labels)
        tests+=trial(n,edges,portals,weights,labels)
    print(tests,"original-graph target/solver calls passed")


if __name__=="__main__":
    main()
