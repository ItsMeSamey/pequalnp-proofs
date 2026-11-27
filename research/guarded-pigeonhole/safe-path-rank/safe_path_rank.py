"""Rank-parameterized safe path with disjoint forbidden edge pairs."""
from collections import deque
from importlib.util import module_from_spec, spec_from_file_location
from pathlib import Path

_spec = spec_from_file_location("chart_hitting", Path(__file__).resolve().parents[1] / "pnp-chart-hitting.py")
_chart = module_from_spec(_spec)
_spec.loader.exec_module(_chart)


def indices(mask):
    while mask:
        low = mask & -mask
        yield low.bit_length() - 1
        mask ^= low


def reduce_vector(basis, value):
    witness = 0
    for pivot in sorted(basis, reverse=True):
        if value >> pivot & 1:
            column, combination = basis[pivot]
            value ^= column
            witness ^= combination
    return value, witness


def decompose(columns):
    basis, kernel = {}, []
    for i, column in enumerate(columns):
        remainder, combination = reduce_vector(basis, column)
        combination ^= 1 << i
        if remainder:
            basis[remainder.bit_length() - 1] = remainder, combination
        else:
            kernel.append(combination)
    return basis, kernel


def linear_sum(columns, mask):
    total = 0
    for i in indices(mask):
        total ^= columns[i]
    return total


def path_in_subset(n, edges, used, s, t):
    adj = [[] for _ in range(n)]
    for i in used:
        v, w = edges[i]
        adj[v].append((w, i))
        adj[w].append((v, i))
    parents = {s: None}
    queue = deque([s])
    while queue:
        v = queue.popleft()
        if v == t:
            break
        for w, i in adj[v]:
            if w not in parents:
                parents[w] = v, i
                queue.append(w)
    path = []
    while t != s:
        t, i = parents[t]
        path.append(i)
    return list(reversed(path))


def orient(menus):
    """Choose one of the three pairwise differences per menu with minimum span rank."""
    choices = [(a ^ b, b, a) for a, b in menus]

    def search(basis, budget):
        for options in choices:
            residuals = [reduce_vector(basis, value)[0] for value in options]
            if all(residuals):
                if budget == 0:
                    return None
                for row in set(residuals):
                    extended = dict(basis)
                    extended[row.bit_length()-1] = row, 0
                    result = search(extended, budget-1)
                    if result is not None:
                        return result
                return None
        return [next(i for i, value in enumerate(options) if not reduce_vector(basis, value)[0])
                for options in choices]

    for bound in range(len(menus)+1):
        result = search({}, bound)
        if result is not None:
            return result
    raise AssertionError("all menus are orientable")


def solve(n, edges, pairs, s, t, optimize=True):
    """Return (difference rank, ordered original edge IDs or None)."""
    if not (0 <= s < n and 0 <= t < n) or any(not (0 <= v < n and 0 <= w < n) for v, w in edges):
        raise ValueError("invalid vertex")
    paired = [i for pair in pairs for i in pair]
    if any(len(pair) != 2 for pair in pairs) or len(set(paired)) != len(paired) or any(not 0 <= i < len(edges) for i in paired):
        raise ValueError("pairs must be disjoint valid edge IDs")
    paired = set(paired)
    free = [i for i in range(len(edges)) if i not in paired]
    columns = [(1 << v) ^ (1 << w) for v, w in edges]
    free_basis, _ = decompose(columns[i] for i in free)
    quotient = [reduce_vector(free_basis, c)[0] for c in columns]
    original_target = (1 << s) ^ (1 << t)
    target = reduce_vector(free_basis, original_target)[0]
    menus = [(quotient[i],quotient[j]) for i,j in pairs]
    baselines = orient(menus) if optimize else [0]*len(pairs)
    states = []
    first, deltas = [], []
    for (a,b), base in zip(menus, baselines):
        values = (0,a,b)
        left, right = [j for j in range(3) if j != base]
        states.append((base,left,right))
        target ^= values[base]
        first.append(values[left] ^ values[base])
        deltas.append(values[left] ^ values[right])
    delta_basis, _ = decompose(deltas)
    rank = len(delta_basis)
    z_basis, directions = decompose(reduce_vector(delta_basis, c)[0] for c in first)
    rem, origin = reduce_vector(z_basis, reduce_vector(delta_basis, target)[0])
    if rem:
        return rank, None
    dim = len(directions)
    if dim <= 2 * (rank + max(1, dim.bit_length())):
        seeds = range(1 << dim)
    else:
        seeds = _chart.seeds(dim, rank)
    for seed in seeds:
        z = origin ^ linear_sum(directions, seed)
        active = list(indices(z))
        active_basis, _ = decompose(deltas[i] for i in active)
        rem, swaps = reduce_vector(active_basis, target ^ linear_sum(first, z))
        if rem:
            continue
        original_states = baselines.copy()
        for j, i in enumerate(active):
            original_states[i] = states[i][1+(swaps >> j & 1)]
        used = [pairs[i][state-1] for i, state in enumerate(original_states) if state]
        remaining = original_target
        for i in used:
            remaining ^= columns[i]
        rem, extra = reduce_vector(free_basis, remaining)
        assert not rem
        used.extend(free[i] for i in indices(extra))
        return rank, path_in_subset(n, edges, used, s, t)
    return rank, None
