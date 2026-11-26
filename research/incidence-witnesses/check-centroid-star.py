"""Compare centroid context tables and batched updates with full recomputation."""
from itertools import product
from random import Random

rng = Random(401)
full = (1 << 12) - 1
totals = [0, 0]
for trial in range(100):
    n = rng.randrange(2, 65)
    leaves = list(range(n))
    ready = leaves.copy()
    parent, children, op = {}, {}, {}
    neighbors = {v: [] for v in leaves}
    for g in range(n, 2*n-1):
        a = ready.pop(rng.randrange(len(ready)))
        b = ready.pop(rng.randrange(len(ready))) if trial % 2 else ready.pop()
        parent[a] = parent[b] = g
        children[g] = a, b
        op[g] = int.__and__ if rng.randrange(2) else int.__or__
        neighbors[g] = [a,b]
        neighbors[a].append(g)
        neighbors[b].append(g)
        ready.append(g)
    root = ready[0]
    base = {u: rng.randrange(full+1) for u in leaves}
    for u,(a,b) in children.items():
        base[u] = op[u](base[a],base[b])

    def partitions(nodes, skip):
        unseen = nodes-{skip}
        result = []
        while unseen:
            frontier = [unseen.pop()]
            comp = set(frontier)
            while frontier:
                for u in neighbors[frontier.pop()]:
                    if u in unseen:
                        unseen.remove(u)
                        comp.add(u)
                        frontier.append(u)
            result.append(comp)
        return result

    def apply(ctx,t):
        return ctx[0] | (ctx[1] & t)

    table, level = {}, {}
    counts = [0]
    def decompose(nodes, h):
        c = next(v for v in nodes if max(map(len,partitions(nodes,v)),default=0)<=len(nodes)//2)
        level[c] = h
        table[c,c] = (0,full)
        stack = [c]
        while stack:
            v = stack.pop()
            for idx,x in enumerate(children.get(v,())):
                if x not in nodes:
                    continue
                w = base[children[v][1-idx]]
                upper = table[v,c]
                table[x,c] = tuple(apply(upper,op[v](t,w)) for t in (0,full))
                counts[0] += 2
                stack.append(x)
        x = c
        while x in parent and parent[x] in nodes:
            v = parent[x]
            other = next(a for a in children[v] if a!=x)
            table[c,v] = tuple(op[v](t,base[other]) for t in table[c,x])
            counts[0] += 2
            x = v
        for comp in partitions(nodes,c):
            decompose(comp,h+1)
    decompose(set(neighbors),0)
    assert counts[0] <= 4*(n-1)*((2*n-1).bit_length()-1)

    def path(x,y,value):
        nodes = [x]
        while nodes[-1] != y:
            nodes.append(parent[nodes[-1]])
        c = min(nodes,key=level.get)
        return apply(table[c,y],apply(table[x,c],value))

    for iteration in range(32):
        k = rng.randrange(1,n+1)
        changes = {u:rng.randrange(full+1) for u in rng.sample(leaves,k)}
        wanted = base | changes
        for v,(a,b) in children.items():
            wanted[v]=op[v](wanted[a],wanted[b])
        touched=set(changes)
        for a in changes:
            while a in parent:
                a=parent[a]
                touched.add(a)
        def visit(v):
            if v in changes:
                return v,changes[v],0
            branch=[x for x in children[v] if x in touched]
            if len(branch)==1:
                return visit(branch[0])
            aa,bb=branch
            a,x,ca=visit(aa)
            b,y,cb=visit(bb)
            return v,op[v](path(a,aa,x),path(b,bb,y)),ca+cb+9
        v,x,cost=visit(root)
        actual=path(v,root,x)
        assert actual==wanted[root]
        assert cost+(4 if v!=root else 0)<=9*k
        totals[0]+=1

for a,b,w,t in product(range(2),repeat=4):
    if a<=b:
        f=lambda x:a|(b&x)
        assert f(t|w)==((a|(b&w))|(b&t))
        assert f(t&w)==(a|((a|(b&w))&t))
        totals[1]+=1
print("batched comparisons and unary checks",*totals)
