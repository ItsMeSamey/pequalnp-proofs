#!/usr/bin/env python3
"""Differential oracle for frontier elimination, and small-graph centroid bounds."""
from fractions import Fraction
from itertools import combinations, product
from random import Random


def components(vertices, edges):
    todo = set(vertices)
    result = []
    while todo:
        v = todo.pop()
        part = {v}
        queue = [v]
        while queue:
            x = queue.pop()
            neighbors = {b if a == x else a for a, b in edges if a == x or b == x} & todo
            part.update(neighbors)
            queue.extend(neighbors)
            todo.difference_update(neighbors)
        result.append(part)
    return result


def checks_full(vertices, edges, color, active, labels):
    sums = []
    for c in sorted(active):
        part = {v for v in vertices if color[v] == c}
        if len(components(part, edges)) != 1:
            return None
        value = 0
        for v in part:
            value ^= labels[v]
        sums.append(value)
    return tuple(sums)


def reduce_branch(vertices, actual, virtual, removed, pins, guess, active, labels):
    """Return transformed edges, pins, active colours, and amounts to subtract from targets."""
    edges = actual | virtual
    full_frontier = {y for e in edges for x, y in (e, e[::-1]) if x in removed and y not in removed}
    local = removed | full_frontier
    assert set(guess) == local
    if any(guess[v] != c for v, c in pins.items() if v in local):
        return None
    if not set(guess.values()) <= active:
        return None
    survive = vertices - removed
    new_pins = {v:c for v,c in pins.items() if v in survive}
    new_pins.update({v:guess[v] for v in full_frontier})
    new_edges = {e for e in edges if set(e) <= survive}
    closed = set()
    sub = {c:0 for c in active}
    for v in removed:
        sub[guess[v]] ^= labels[v]
    local_edges = {e for e in edges if set(e) <= local and guess[e[0]] == guess[e[1]]}
    for comp in components(local, local_edges):
        if not comp & removed:
            continue
        c = guess[next(iter(comp))]
        contact = comp & full_frontier
        if contact:
            new_edges.update(combinations(sorted(contact), 2))
        else:
            if c in new_pins.values() or c in closed:
                return None
            closed.add(c)
    return new_edges, new_pins, active - closed, sub


def check_frontier():
    rng = Random(328)
    instances = completions = compatible = closures = created_edges = 0
    for _ in range(350):
        n, b = rng.randint(1, 7), rng.randint(1, 3)
        vertices = set(range(n))
        active = {c for c in range(b) if rng.random() < .85}
        # Vary the active palette to exercise colors already forbidden by earlier steps.
        if not active:
            active = {rng.randrange(b)}
        palette = sorted(active)
        labels = [rng.randrange(8) for _ in vertices]
        actual = {e for e in combinations(range(n), 2) if rng.random() < .35}
        pins = {v:rng.choice(palette) for v in vertices if rng.random() < .45}
        virtual = {e for e in combinations(sorted(pins), 2)
                   if pins[e[0]] == pins[e[1]] and e not in actual and rng.random() < .65}
        removed = {v for v in vertices if rng.random() < .43}
        frontier = {y for e in actual | virtual for x, y in (e, e[::-1]) if x in removed and y not in removed}
        local = tuple(sorted(removed | frontier))
        free = sorted(vertices - set(pins))
        cache = {}
        for seq in product(palette, repeat=len(free)):
            full = dict(zip(free, seq)) | pins
            key = tuple(full[v] for v in local)
            if key not in cache:
                cache[key] = reduce_branch(vertices, actual, virtual, removed, pins, dict(zip(local,key)),
                                           active, labels)
                if cache[key] is not None:
                    ne, _, na, _ = cache[key]
                    closures += len(active - na)
                    created_edges += len(ne - actual - virtual)
            branch = cache[key]
            expected = checks_full(vertices, actual | virtual, full, active, labels)
            result = None
            if branch:
                ne, np, na, sub = branch
                survive = vertices - removed
                if all(full[v] == c for v,c in np.items()) and {full[v] for v in survive} <= na:
                    residual = checks_full(survive, ne, full, na, labels)
                    if residual is not None:
                        ordered = dict(zip(sorted(na), residual))
                        result = tuple(sub[c] ^ ordered.get(c, 0) for c in sorted(active))
            assert result == expected, (actual, virtual, pins, removed, full, expected, result)
            compatible += expected is not None
            completions += 1
        instances += 1
    assert closures and created_edges
    return instances, completions, compatible, closures, created_edges


def expansion(vertices, edges):
    best = Fraction(1)
    for k in range(1,len(vertices)//2+1):
        for chosen in combinations(vertices,k):
            s = set(chosen)
            nbr = {y for edge in edges for x,y in (edge,edge[::-1]) if x in s and y in vertices-s}
            best = min(best, Fraction(len(nbr),k))
    return best


def check_centroid(vs, edges):
    if len(components(vs,edges)) != 1:
        return 0
    alpha = expansion(vs,edges)
    delta = max(sum(v in e for e in edges) for v in vs)
    pieces = []
    for k in reversed(range(2,len(vs)+1)):
        for chunk in combinations(vs,k):
            a = set(chunk)
            if not any(a <= c for c in pieces) and all(len(components(a-{v},edges)) == 1 for v in a):
                # For size two, singleton deletions alone do not imply an actual edge.
                if k > 2 or tuple(sorted(a)) in edges:
                    pieces.append(a)
    arts = {v for v in vs if sum(v in a for a in pieces) > 1}
    nodes = list(range(len(pieces)+len(arts)))
    art_nodes = dict(zip(sorted(arts),nodes[len(pieces):]))
    bt = {(j, art_nodes[v]) for j,c in enumerate(pieces) for v in c & arts}
    weights = [len(c-arts) for c in pieces] + [1]*len(arts)
    assert sum(weights) == len(vs) and len(bt) == len(nodes)-1
    centers = [i for i in nodes if all(2*sum(weights[j] for j in c) <= len(vs)
                                       for c in components(set(nodes)-{i},bt))]
    assert centers
    for node in centers:
        if node not in range(len(pieces)):
            assert len(vs) <= 1 + delta/alpha
            continue
        block = pieces[node]
        for a in components(vs-block,edges):
            contacts = {v for e in edges for u,v in (e,e[::-1]) if u in a and v in block}
            assert len(contacts) == 1 and 2*len(a) <= len(vs) and len(a) <= 1/alpha
        if len(block) == 2:
            assert len(vs) <= 2 + 2*delta/alpha
        else:
            assert expansion(block,edges) >= alpha/delta
    return len(centers)


if __name__ == "__main__":
    print("Frontier instances, completions, feasible completions, closures, shortcut edges:", check_frontier())
    graphs = centers = 0
    rng = Random(468)
    for n in range(2,8):
        edge_list = list(combinations(range(n),2))
        masks = range(1 << len(edge_list)) if n <= 5 else (rng.getrandbits(len(edge_list)) for _ in range(100))
        for mask in masks:
            edges = {e for i,e in enumerate(edge_list) if mask >> i & 1}
            c = check_centroid(set(range(n)), edges)
            graphs += bool(c)
            centers += c
    print("Connected graphs and weighted centroid choices:", graphs, centers)
