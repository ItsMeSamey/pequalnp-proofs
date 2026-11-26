"""Find a small binary-matroid minor preserving unlabelled triangle states.

The boundary space occupies the low two bits of every input column.
The returned pair consists of contracted indices and surviving indices.
Every other outside column is deleted. All triangle columns are retained.
"""
from collections import deque


def quotient_basis(columns):
    pivots = {}
    basis = []
    for i, col in enumerate(columns):
        x = col >> 2
        while x:
            j = x.bit_length() - 1
            if j not in pivots:
                pivots[j] = x
                basis.append(i)
                break
            x ^= pivots[j]
    return basis


def coordinates(columns, basis):
    pivots = {}
    for k, i in enumerate(basis):
        x = columns[i] >> 2
        coeff = 1 << k
        while x:
            j = x.bit_length() - 1
            if j not in pivots:
                pivots[j] = (x, coeff)
                break
            y, mask = pivots[j]
            x ^= y
            coeff ^= mask
        assert x
    types = []
    supports = []
    for col in columns:
        x = col >> 2
        coeff = 0
        while x:
            y, mask = pivots[x.bit_length() - 1]
            x ^= y
            coeff ^= mask
        p = col & 3
        for k, i in enumerate(basis):
            if coeff >> k & 1:
                p ^= columns[i] & 3
        types.append(p)
        supports.append(coeff)
    return types, supports


def triangle_minor(columns):
    basis = quotient_basis(columns)
    while True:
        types, supports = coordinates(columns, basis)
        active = sorted(set(types) - {0})
        representatives = [types.index(p) for p in active]
        if len(active) != 2:
            return 'parallel', basis, representatives
        a, b = active
        adj = [[] for _ in columns]
        basis_set = set(basis)
        for i, mask in enumerate(supports):
            if i not in basis_set:
                for k, x in enumerate(basis):
                    if mask >> k & 1:
                        adj[i].append(x)
                        adj[x].append(i)
        queue = deque(i for i in range(len(columns)) if types[i] == a)
        pred = {i: None for i in queue}
        while queue:
            v = queue.popleft()
            if types[v] == b:
                break
            for u in adj[v]:
                if u not in pred:
                    pred[u] = v
                    queue.append(u)
        else:
            return 'parallel', basis, representatives
        path = [v]
        while pred[path[-1]] is not None:
            path.append(pred[path[-1]])
        path.reverse()
        if len(path) == 3:
            e, x, f = path
            return 'star', [i for i in basis if i != x], [x, e, f]
        x, z = path[1:3]
        assert types[z] == 0
        basis[basis.index(x)] = z
