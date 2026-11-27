"""Whole-CNF count on a verified guarded prism inside a power of a cycle."""
from collections import Counter
from math import comb
from operator import index

from guarded_prism import supplied_leaf


def count_original(n, clauses, *, source_radius=False):
    """Return the exact count, or None if the original clauses miss this shape.

    source_radius additionally enforces R=6 ceil(log2 ceil(log2 n)).
    It does not assert the source dispatcher or verify a greedy trajectory.
    """
    n = index(n)
    if n < 0:
        raise ValueError("negative number of variables")
    rows = [tuple(row) for row in clauses]
    if not rows or any(len(row) != 3 or len(set(row)) != 3 or
                       any(not isinstance(x, int) or not 1 <= x <= n for x in row)
                       for row in rows):
        return None
    degree = Counter(x for row in rows for x in row)
    guard = max(degree, key=degree.get)
    real = [row for row in rows if guard not in row]
    used = {guard} | {x for row in real for x in row}
    if used != degree.keys():
        return None
    compact = {x: i for i, x in enumerate(sorted(used), 1)}
    leaf = supplied_leaf(len(used), [(compact[guard],)] +
                         [tuple(compact[x] for x in row) for row in real])
    if leaf is None:
        return None
    spins = {x for col in leaf.columns for x in col}
    v = len(spins)
    adj = {x: set() for x in spins}
    for row in rows:
        if guard not in row:
            continue
        a, b = (compact[x] for x in row if x != guard)
        if a not in spins or b not in spins or b in adj[a]:
            return None
        adj[a].add(b)
        adj[b].add(a)
    degrees = {len(neighbors) for neighbors in adj.values()}
    if len(degrees) != 1:
        return None
    d = degrees.pop()
    radius = d // 2
    if d % 2 or radius < 2 or v <= 4*radius+2:
        return None
    if source_radius and radius != 6*((n-1).bit_length()-1).bit_length():
        return None
    for row in real:
        a, b = (compact[x] for x in row if compact[x] in spins)
        if b not in adj[a]:
            return None
    closed = {x: adj[x] | {x} for x in spins}
    consecutive = {x: [y for y in adj[x] if len(closed[x] & closed[y]) == d]
                   for x in spins}
    if any(len(neighbors) != 2 for neighbors in consecutive.values()):
        return None
    first = min(spins)
    cycle = [first, min(consecutive[first])]
    visited = set(cycle)
    while len(cycle) < v:
        prev, cur = cycle[-2:]
        nxt, = (y for y in consecutive[cur] if y != prev)
        if nxt in visited:
            return None
        cycle.append(nxt)
        visited.add(nxt)
    if any(adj[x] != {cycle[(i+j) % v] for j in range(-radius, radius+1) if j}
           for i, x in enumerate(cycle)):
        return None

    # g=0 forces zero base spins to be separated by more than radius.
    independent = 1
    for k in range(1, v//(radius+1)+1):
        necklaces, rem = divmod(v*comb(v-radius*k-1, k-1), k)
        if rem:
            raise ArithmeticError("nonintegral cyclic gap count")
        independent += necklaces
    return (leaf.weight(0) + (independent << len(real))) << (n-len(used))
