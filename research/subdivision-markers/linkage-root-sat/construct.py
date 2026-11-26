"""Linear-size graph construction for exact named-root kernels from nonempty 3-CNF."""
from collections import defaultdict


def build(n, clauses):
    if n < 1 or any(not 1<=len(cl)<=3 or any(not 1<=abs(lit)<=n for lit in cl) for cl in clauses):
        raise ValueError("use at least one variable and clauses of one to three nonzero literals")
    size=0
    def vertex():
        nonlocal size
        size+=1
        return size-1
    variables=[(vertex(),vertex()) for _ in range(n)]
    clausepairs=[(vertex(),vertex()) for _ in clauses]
    rails=defaultdict(list)
    E=[]
    for (c,d),cl in zip(clausepairs,clauses):
        for literal in cl:
            a,b=vertex(),vertex()
            rails[literal].extend((a,b))
            E.extend(((c,a),(d,b)))
    for i,(s,t) in enumerate(variables,1):
        for lit in (i,-i):
            chain=[s]+(rails[lit] or [vertex()])+[t]
            E.extend(zip(chain,chain[1:]))
    adj=[[] for _ in range(size)]
    for a,b in E:
        adj[a].append(b)
        adj[b].append(a)
    seen=set()
    backbone=[]
    for s,_ in variables:
        if s in seen:
            continue
        stack=[s]
        seen.add(s)
        while stack:
            for b in adj[stack.pop()]:
                if b not in seen:
                    seen.add(b)
                    stack.append(b)
        v=vertex()
        E.append((s,v))
        if backbone:
            E.append((backbone[-1],v))
        backbone.append(v)
    edges=[]
    for a,b in E:
        v=vertex()
        edges.extend(((a,v),(v,b)))
    return size, tuple(edges), tuple(variables+clausepairs)


def named(pairs, mode="compact"):
    k=len(pairs)
    if not k:
        raise ValueError("one or more terminal pairs required")
    if mode=="units":
        roots=[1<<v for pair in pairs for v in pair]
        return roots,[3<<(2*i) for i in range(k)]
    if mode=="edges":
        roots=[(1<<s)^(1<<t) for s,t in pairs]
        roots += [(1<<pairs[i][0])^(1<<pairs[i+1][0]) for i in range(k-1)]
        return roots,[1<<i for i in range(k)]
    if mode!="compact":
        raise ValueError("unrecognized root encoding")
    h=k.bit_length()
    roots=[sum(((1<<s)|(1<<t)) for i,(s,t) in enumerate(pairs,1) if i>>j&1) for j in range(h)]
    roots += [(1<<pairs[i][0])^(1<<pairs[-1][0]) for i in range(k-1)]
    return roots,[1<<i for i in range(h)]
