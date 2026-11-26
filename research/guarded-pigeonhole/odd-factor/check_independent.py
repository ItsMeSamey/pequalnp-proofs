"""Independent finite audit of the charge transform, matching routing and Tseitin face."""
from itertools import combinations, permutations, product
from random import Random

def check(n):
    h = [('H',i) for i in range(4)]
    root = h[0]
    portals = [(side,i,'r') for side in range(2) for i in range(n)]
    charged = [root,*portals]
    hedges = list(combinations(h,2))
    leaves = {(side,i,j):(side,i,j) for side in range(2) for i in range(n) for j in range(n)}
    pedges = [((s,i,'r'),v) for (s,i,j),v in leaves.items()]
    connectors = {(i,j):((0,i,j),(1,j,i)) for i in range(n) for j in range(n)}
    V = set(h+portals+list(leaves.values()))
    E = set(hedges+pedges+list(connectors.values()))
    def route(m):
        return {edge for i,j in enumerate(m) for edge in
                (connectors[i,j],((0,i,'r'),(0,i,j)),((1,j,'r'),(1,j,i)))}
    def guards(q,z):
        a=q.copy()
        a.update({v:q[v]^q[charged[i-1]] for i,v in enumerate(charged) if i})
        F={v:int(v in charged) for v in V}
        for u,v in z:
            F[u]^=1
            F[v]^=1
        dual=F.copy()
        dual.update({v:F[v]^F[charged[i+1]] for i,v in enumerate(charged[:-1])})
        return {v for v in V if q[v] and dual[v]}, {(u,v) for u,v in z if a[u]^a[v]}
    for matching in permutations(range(n)):
        z = route(matching)
        for color in product((0,1),repeat=2*n):
            if sum(color)%2==0:
                continue
            a = dict.fromkeys(V,0)
            for i,v in enumerate(portals):
                a[v]=color[i]
            for s,i,j in leaves:
                a[s,i,j]=color[s*n+i]
            q=a.copy()
            acc=0
            for v in charged:
                acc ^= a[v]
                q[v]=acc
            assert q[charged[-1]]
            assert guards(q,z)==(set(),{connectors[i,j] for i,j in enumerate(matching) if color[i]^color[n+j]})
    z=route(tuple(range(n)))
    q={v:int(v in h or v in charged) for v in V}
    for mask in range(1<<len(hedges)):
        selected={edge for i,edge in enumerate(hedges) if (mask>>i)&1}
        bad={v for v in h if sum(v in e for e in selected)%2 != (v==root)}
        assert guards(q,z|selected)==(bad,set())
    rng=Random(73)
    for _ in range(1000):
        q={v:rng.randrange(2) for v in V}
        z={e for e in E if rng.randrange(2)}
        bv,be=guards(q,z)
        assert (len(bv)+len(be))%2==q[charged[-1]]
for n in (2,3):
    check(n)
print("Both sides, all colorings/matchings for n=2,3; 128 Tseitin assignments and 2000 cancellation checks passed.")
