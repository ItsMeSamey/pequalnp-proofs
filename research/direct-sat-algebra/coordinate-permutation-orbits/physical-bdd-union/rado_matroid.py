"""Rado deficiency kernel for binary planes given by independent generator pairs."""
from collections import deque


def _reduce(value, pivots):
    """Return canonical quotient coordinates and the tracked basis provenance."""
    provenance = 0
    for p in sorted(pivots, reverse=True):
        if value >> p & 1:
            row, support = pivots[p]
            value ^= row
            provenance ^= support
    return value, provenance


def _insert(value, tag, pivots):
    rest, support = _reduce(value, pivots)
    if rest:
        pivots[rest.bit_length() - 1] = rest, tag ^ support
    return rest, support


def _intersection(planes, rows, quotient):
    """Maximum independent transversal modulo quotient, retaining original selectors."""
    items = []
    by_row = {}
    for i in rows:
        a, b = planes[i]
        by_row[i] = []
        for selector, v in enumerate((a, b, a ^ b), 1):
            v, _ = _reduce(v, quotient)
            if v:
                by_row[i].append(len(items))
                items.append((i, selector, v))
    chosen = set()
    while True:
        basis = {}
        occupied = set()
        for index in sorted(chosen):
            row, _, v = items[index]
            occupied.add(row)
            _insert(v, 1 << index, basis)
        parent = {j: None for i in rows if i not in occupied for j in by_row[i]}
        queue = deque(parent)
        terminal = None
        while queue:
            j = queue.popleft()
            i, _, v = items[j]
            if j in chosen:
                neighbors = by_row[i]
            else:
                rest, circuit = _reduce(v, basis)
                if rest:
                    terminal = j
                    break
                neighbors = []
                while circuit:
                    bit = circuit & -circuit
                    neighbors.append(bit.bit_length() - 1)
                    circuit ^= bit
            for k in neighbors:
                if k not in parent:
                    parent[k] = j
                    queue.append(k)
        if terminal is None:
            return {items[j][0]: items[j][1] for j in sorted(chosen)}
        j = terminal
        while j is not None:
            if j in chosen:
                chosen.remove(j)
            else:
                chosen.add(j)
            j = parent[j]


def _components(planes, rows):
    """Join row owners along fundamental circuits of the indexed generators."""
    parent = {i: i for i in rows}
    def find(i):
        while parent[i] != i:
            parent[i] = parent[parent[i]]
            i = parent[i]
        return i

    basis = {}
    owner = []
    for i in rows:
        for v in planes[i]:
            rest, support = _insert(v, 1 << len(owner), basis)
            if rest:
                owner.append(i)
            else:
                while support:
                    bit = support & -support
                    j = owner[bit.bit_length() - 1]
                    parent[find(j)] = find(i)
                    support ^= bit
    groups = {}
    for i in rows:
        groups.setdefault(find(i), []).append(i)
    return list(groups.values())


def kernel(planes):
    """Return core row components, outside selectors, maximum deficiency, call count.

    Selector bits 1 and 2 choose the first and second generator, respectively;
    3 chooses their XOR. Outside representatives are independent modulo the core.
    """
    planes = [tuple(pair) for pair in planes]
    for pair in planes:
        if len(pair) != 2 or any(type(v) is not int or v <= 0 for v in pair) or pair[0] == pair[1]:
            raise ValueError("each plane must have two independent positive masks")
    rows = list(range(len(planes)))
    calls = 0
    def intersect(indices, quotient):
        nonlocal calls
        calls += 1
        return _intersection(planes, indices, quotient)

    initial = intersect(rows, {})
    deficiency = len(rows) - len(initial)
    if deficiency == 0:
        return [], initial, 0, calls
    core = rows[:]
    for i in rows:
        trial = [j for j in core if j != i]
        if len(trial) >= deficiency and len(trial) - len(intersect(trial, {})) == deficiency:
            core = trial
    quotient = {}
    for i in core:
        for v in planes[i]:
            _insert(v, 0, quotient)
    core_set = set(core)
    outside = [i for i in rows if i not in core_set]
    representatives = intersect(outside, quotient) if outside else {}
    if len(representatives) != len(outside):
        raise ArithmeticError("outside transversal is incomplete")
    return _components(planes, core), representatives, deficiency, calls
