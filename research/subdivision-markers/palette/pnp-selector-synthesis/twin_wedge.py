"""Whole indexed cographic paired space via a charged-twin quotient."""
from itertools import combinations, product
from planar_moment_certificate import CertifiedDual
from wedge_path import wedge


def solve(n, edges, solve_compressed):
    """Callback returns an iterable of generating pairs of compressed edge masks."""
    host = CertifiedDual(n, edges)
    neighbors = [{v for v, _ in row if v != u} for u, row in enumerate(host.graph)]
    classes = []
    for u in range(n):
        for group in classes:
            v = group[0]
            if host.charge[u] == host.charge[v] and neighbors[u]-{v} == neighbors[v]-{u}:
                group.append(u)
                break
        else:
            classes.append([u])
    keep, slots, swaps = [], [], []
    for group in classes:
        charged = bool(host.charge[group[0]])
        cap = 6-len(group)%2 if charged else 3
        representatives = group[:cap]
        keep.extend(representatives)
        stride = 2 if charged else 1
        for j in range(cap, len(group), stride):
            slots.append((sum(1<<i for i in group[j:j+stride]), representatives))
        swaps.extend(zip(group, group[1:]))
    key = {v:i for i,v in enumerate(keep)}
    shadow = [(key[u],key[v]) for u in keep for v in sorted(neighbors[u]) if v in key and u<v]
    adj = [[] for _ in keep]
    for i,(u,v) in enumerate(shadow):
        adj[u].append((v,i))
        adj[v].append((u,i))
    order = [0]
    parent = {0:None}
    for u in order:
        for v,i in adj[u]:
            if v not in parent:
                parent[v]=(u,i)
                order.append(v)
    charge = [host.charge[v] for v in keep]
    tag = [0]*len(shadow)
    for v in reversed(order[1:]):
        u,i=parent[v]
        tag[i]=charge[v]
        charge[u]^=charge[v]
    assert len(order)==len(keep) and charge[0]==0
    packed=[(u,v,tag[i]) for i,(u,v) in enumerate(shadow)]
    compressed = CertifiedDual(len(keep), packed)
    rows, actual = {}, []
    full=(1<<n)-1
    def offer(x,y):
        if x&1:x^=full
        if y&1:y^=full
        z=wedge(x,y)
        while z:
            p=z.bit_length()
            if p not in rows:
                rows[p]=z
                actual.append((x,y))
                return
            z^=rows[p]
    def potential(mask):
        x=0
        for v in order[1:]:
            u,i=parent[v]
            x|=(((x>>keep[u])^(mask>>i))&1)<<keep[v]
        return x
    for a,b in solve_compressed(len(keep),packed):
        x,y=potential(a),potential(b)
        cx=sum(((x>>u)&1)<<i for i,u in enumerate(keep))
        cy=sum(((y>>u)&1)<<i for i,u in enumerate(keep))
        if compressed.cut(cx)!=a or compressed.cut(cy)!=b or not compressed.compatible(cx,cy):
            raise ValueError("compressed backend returned an infeasible indexed pair")
        deltas=[]
        for mask,reps in slots:
            v=reps[0]
            if x>>v&1:x|=mask
            if y>>v&1:y|=mask
            deltas.append([((mask if ((x>>w)^(x>>v))&1 else 0),
                            (mask if ((y>>w)^(y>>v))&1 else 0)) for w in reps[1:]])
        offer(x,y)
        for choices in deltas:
            for dx,dy in choices:offer(x^dx,y^dy)
        for left,right in combinations(deltas,2):
            for (dx,dy),(ex,ey) in product(left,right):offer(x^dx^ex,y^dy^ey)
    for x,y in actual:  # Newly appended actual generators also need their orbits.
        for u,v in swaps:
            flip=(1<<u)|(1<<v)
            offer(x^(flip if ((x>>u)^(x>>v))&1 else 0),
                  y^(flip if ((y>>u)^(y>>v))&1 else 0))
    return [(host.cut(x),host.cut(y)) for x,y in actual]
