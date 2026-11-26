"""Cographic aggregate selector. The pin_tree callback returns a spanning tree."""
from itertools import product


def parity(x):
    return x.bit_count() & 1


def apply(matrix, color):
    a, b = matrix
    return (a if color & 1 else 0) ^ (b if color & 2 else 0)


def charges(n, edges, tags):
    if len(edges) != len(tags):
        raise ValueError("one tag per edge is required")
    rows = [[0, 0] for _ in range(n)]
    for (u, v), (a, b) in zip(edges, tags):
        for w in (u, v):
            rows[w][0] ^= a
            rows[w][1] ^= b
    return tuple(map(tuple, rows))


def sparse(rows, k):
    supports = {lam: frozenset(i for i, (a, b) in enumerate(rows)
                               if parity(a & lam) or parity(b & lam))
                for lam in range(1 << k)}
    U, W = frozenset(), {0}
    while True:
        cutoff = 10 * (k + len(U) + 1)
        candidates = (lam for lam in supports if lam not in W
                      and len(supports[lam] - U) <= cutoff)
        lam = next(candidates, None)
        if lam is None:
            return sorted(U), W
        U |= supports[lam]
        W |= {x ^ lam for x in W}


def score(rows, colors):
    total = 0
    for matrix, color in zip(rows, colors):
        total ^= apply(matrix, color)
    return total


def tree_coloring(n, tree, rows, pins, target=None):
    """Return a pin-extending tree coloring. If target is None, ignore scores."""
    adjacency = [[] for _ in range(n)]
    for u, v in tree:
        adjacency[u].append(v)
        adjacency[v].append(u)
    parent = {0: None}
    order = [0]
    for u in order:
        for v in adjacency[u]:
            if v not in parent:
                parent[v] = u
                order.append(v)
    if len(parent) != n or len(tree) != n - 1:
        raise ValueError("expected a spanning tree")
    table = {}
    for u in reversed(order):
        children = [v for v in adjacency[u] if parent[v] == u]
        options = (pins[u],) if u in pins else range(4)
        entries = {}
        for color in options:
            start = 0 if target is None else apply(rows[u], color)
            states = {start: color << (2 * u)}
            for v in children:
                nxt = {}
                for (other, child_score), assignment in table[v].items():
                    if other == color:
                        continue
                    for subtotal, partial in states.items():
                        nxt.setdefault(subtotal ^ child_score, partial | assignment)
                states = nxt
            for subtotal, assignment in states.items():
                entries[color, subtotal] = assignment
        table[u] = entries
    for (_, subtotal), assignment in table[0].items():
        if target is None or subtotal == target:
            return tuple((assignment >> (2 * i)) & 3 for i in range(n))
    return None


def solve(n, edges, tags, k, target, pin_tree):
    rows = charges(n, edges, tags)
    U, W = sparse(rows, k)
    for assignment in product(range(4), repeat=len(U)):
        pins = dict(zip(U, assignment))
        pin_score = score([rows[v] for v in U], assignment)
        if any(parity(lam & (pin_score ^ target)) for lam in W):
            continue
        tree = pin_tree(n, edges, pins)
        if tree is None:
            continue
        colors = tree_coloring(n, tree, rows, pins, target)
        assert colors is not None and score(rows, colors) == target
        return colors, tree
    return None
