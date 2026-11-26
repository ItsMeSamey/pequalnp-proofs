#!/usr/bin/env python3
"""Exhaustive finite tests for the tiny-group algorithm and the two-endpoint ladder."""
from itertools import combinations, product
from random import Random


def components(vs, adj):
    left = set(vs)
    result = []
    while left:
        start = left.pop()
        comp = {start}
        todo = [start]
        while todo:
            new = adj[todo.pop()] & left
            left.difference_update(new)
            todo.extend(new)
            comp.update(new)
        result.append(comp)
    return result


def subsets(values):
    for k in range(len(values)+1):
        yield from combinations(values,k)


def block_models(vs, adj):
    blocks = []
    for c in reversed(list(subsets(sorted(vs)))):
        s = set(c)
        if len(s) < 2 or any(s <= known for known in blocks):
            continue
        if len(components(s,adj)) != 1 or any(len(components(s-{v},adj)) != 1 for v in s):
            continue
        blocks.append(s)
    models = []
    for s in blocks:
        folded = {v:{v} for v in s}
        for comp in components(vs-s,adj):
            attachment = set.union(*(adj[v] for v in comp)) & s
            assert len(attachment) == 1
            folded[attachment.pop()].update(comp)
        models.append((s,folded))
    return models


def bipartitions(vs,adj):
    return [(set(c),vs-set(c)) for c in subsets(sorted(vs)) if 0 < len(c) < len(vs)
            and len(components(c,adj)) == 1 and len(components(vs-set(c),adj)) == 1]


def sum_label(vals,mod):
    return mod if mod in vals else sum(vals)%mod


def block_catalog(models, labels, adj, mod):
    # Infinity is encoded by mod. Fold pendant vertex clusters before testing the block.
    targets = set()
    for vs,folded in models:
        agg = {v:sum_label([labels[i] for i in nodes],mod) for v,nodes in folded.items()}
        if sum(v == mod for v in agg.values()) >= 2:
            targets.add((mod,mod))
        finite = [v for v in vs if agg[v] != mod]
        candidates = [(v,) for v in finite] + [(x,y) for x,y in combinations(finite,2) if y in adj[x]]
        for street in candidates:
            rest = vs-set(street)
            if len(components(rest,adj)) != 1:
                continue
            a = sum_label([agg[v] for v in street],mod)
            b = sum_label([agg[v] for v in rest],mod)
            targets.update(((a,b),(b,a)))
    return targets


def audit_graphs():
    rng = Random(294)
    graphs = cases = 0
    for n in range(1,9):
        vs = set(range(n))
        ed = list(combinations(range(n),2))
        masks = range(1<<len(ed)) if n<=4 else (rng.getrandbits(len(ed)) for _ in range(35))
        for mask in masks:
            adj = [set() for v in vs]
            for i,(a,b) in enumerate(ed):
                if mask >> i & 1:
                    adj[a].add(b); adj[b].add(a)
            if len(components(vs,adj)) != 1:
                continue
            models = block_models(vs,adj)
            naive = bipartitions(vs,adj)
            graphs += 1
            for mod in (1,2):
                labellings = product(range(mod+1),repeat=n) if n<=4 else (
                    [rng.randrange(mod+1) for v in vs] for _ in range(14))
                for labels in labellings:
                    truth = {(sum_label([labels[v] for v in a],mod),sum_label([labels[v] for v in b],mod))
                             for a,b in naive}
                    assert truth == block_catalog(models,labels,adj,mod), (adj,labels,mod,truth)
                    cases += 1
    return graphs,cases


def ladder(n,clauses,index_edges,orders,weights):
    # Coordinates of a direct product of finite cyclic groups. None is the absorber.
    zero = (0,)*len(orders)
    a,b = weights
    target = tuple((x+y)%m for x,y,m in zip(a,b,orders))
    assert target not in (zero,a,b)
    nv = 2*(n+1)+2*n+len(clauses)
    adj = [set() for _ in range(nv)]
    def edge(x,y):
        adj[x].add(y); adj[y].add(x)
    r = list(range(n+1))
    blue = list(range(n+1,2*(n+1)))
    lit = [(2*(n+1)+2*i,2*(n+1)+2*i+1) for i in range(n)]
    for i in range(n+1):
        edge(r[i],blue[i])
    for i in range(n):
        for l in lit[i]:
            for anchor in (r[i],r[i+1],blue[i],blue[i+1]):
                edge(l,anchor)
    for i,j in index_edges:
        edge(r[i],blue[j]); edge(r[j],blue[i])
    for j,c in enumerate(clauses):
        for i,t in c:
            edge(4*n+2+j,lit[i][t])
    vs = set(range(nv))
    assert all(len(components(vs-{z},adj)) == 1 for z in vs)
    # Connected finite target excludes absorbers; enumerate subsets of all low vertices.
    low = r + [v for pair in lit for v in pair]
    sat = any(all(any(values[i]==t for i,t in c) for c in clauses) for values in product((0,1),repeat=n))
    for bits in range(1<<len(low)):
        # Compute the group sum independently for the two nonzero labels.
        partsum = tuple(((x if bits & 1 else 0)+(y if bits >> n & 1 else 0))%m
                        for x,y,m in zip(a,b,orders))
        if partsum != target:
            continue
        red = {v for j,v in enumerate(low) if bits >> j & 1}
        if len(components(red,adj)) == len(components(vs-red,adj)) == 1:
            assert sat
            return True
    assert not sat
    return False


if __name__ == '__main__':
    print("Small-group audit, connected graphs and full catalog comparisons:", audit_graphs())
    rng = Random(802)
    cases = [
        [[(i,t) for i,t in zip(rng.sample(range(3),2),[rng.randrange(2),rng.randrange(2)])]
         for _ in range(rng.randint(1,6))]
        for _ in range(25)]
    cases.append([[(0,x),(1,y)] for x,y in product((0,1),repeat=2)])
    tested = positives = 0
    for orders,weights in [((3,),((1,),(1,))),((4,),((1,),(1,))),((2,2),((1,0),(0,1)))]:
        for clauses in cases:
            positive = ladder(3,clauses,list(combinations(range(4),2)),orders,weights)
            tested += 1; positives += positive
    print("Ladder checks:", tested, "with", tested-positives, "infeasible group instances")
