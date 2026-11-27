"""Rooted vertical separations in explicit binary matroids."""
from collections import deque
from itertools import combinations


def reduce_vector(basis, value):
    mask = 0
    while value and value.bit_length() in basis:
        row, tag = basis[value.bit_length()]
        value ^= row
        mask ^= tag
    return value, mask


def insert(basis, value, tag=0):
    value, mask = reduce_vector(basis, value)
    if value:
        basis[value.bit_length()] = value, tag ^ mask
    return bool(value)


def basis_of(columns, positions):
    basis = {}
    for i in positions:
        insert(basis, columns[i])
    return basis


def minimum_rooted_separation(columns, left_roots, right_roots):
    """Minimize r(X)+r(Y)-r(E) with specified positions forced on each side."""
    left, right = set(left_roots), set(right_roots)
    ground = set(range(len(columns)))
    if left & right or not (left | right) <= ground:
        raise ValueError("invalid forced sides")
    free = ground - left - right
    contractions = [basis_of(columns, side) for side in (left, right)]
    common = set()
    while True:
        bases = [dict(base) for base in contractions]
        for i in sorted(common):
            for base in bases:
                if not insert(base, columns[i], 1 << i):
                    raise RuntimeError("augmentation lost independence")
        edges = {i: [] for i in free}
        starts, ends = [], set()
        for i in sorted(free - common):
            for k, base in enumerate(bases):
                remainder, mask = reduce_vector(base, columns[i])
                if remainder:
                    if k == 0:
                        starts.append(i)
                    else:
                        ends.add(i)
                    # Arcs into starts and out of ends are redundant.
                    continue
                while mask:
                    bit = mask & -mask
                    j = bit.bit_length() - 1
                    src, dst = (j, i) if k == 0 else (i, j)
                    edges[src].append(dst)
                    mask ^= bit
        queue = deque(starts)
        parent = dict.fromkeys(starts)
        while queue:
            i = queue.popleft()
            if i in ends:
                while i is not None:
                    common.symmetric_difference_update((i,))
                    i = parent[i]
                break
            for j in edges[i]:
                if j not in parent:
                    parent[j] = i
                    queue.append(j)
        else:
            # Unreachable elements have first-contraction rank |I outside R|.
            # Reachable elements have second-contraction rank |I inside R|.
            reached = set(parent)
            order = sum(map(len, contractions)) + len(common) - len(basis_of(columns, ground))
            return order, left | (free - reached), right | reached


def find_separation(columns, root_positions):
    """Return a minimum-order vertical separation of order at most two."""
    roots = set(root_positions)
    ground = set(range(len(columns)))
    if len(roots) != 6 or not roots <= ground:
        raise ValueError("expected six distinct root positions")
    free = sorted(ground - roots)
    root_rank = len(basis_of(columns, roots))
    for order in range(3):
        for pins in combinations(free, order + 1):
            if len(basis_of(columns, pins)) <= order:
                continue
            need = max(0, order + 1 - root_rank)
            for extra in combinations(sorted(set(free) - set(pins)), need):
                left = roots.union(extra)
                if need and len(basis_of(columns, left)) <= order:
                    continue
                value, x, y = minimum_rooted_separation(columns, left, pins)
                if value <= order:
                    return x, y
    return None
