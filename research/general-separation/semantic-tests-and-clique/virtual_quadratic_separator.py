"""Rewrite a quadratic output region and compute a certified bounded-degree cut."""
from collections import deque
from original_dag_portfolio import compact
from original_dag_quadratic import gauss
from quadratic_frontier_portfolio import _quadratic_labels, _represent


def quadratic_region(q, gates):
    affine = [{1 << i} for i in range(q)]
    for i, (t, a, b) in enumerate(gates, q):
        if t.bit_count() & 1:
            affine.append({1 << i})
            continue
        c = t & 1
        p = {0} if c else set()
        if ((t >> 2) & 1) ^ c:
            p ^= affine[a]
        if ((t >> 1) & 1) ^ c:
            p ^= affine[b]
        affine.append(p)
    p = set()
    for mask in affine[-1]:
        if not mask or mask.bit_length() - 1 < q:
            p.symmetric_difference_update((mask,))
            continue
        t, a, b = gates[mask.bit_length() - 1 - q]
        c = t & 1
        if c:
            p.symmetric_difference_update((0,))
        if ((t >> 2) & 1) ^ c:
            p ^= affine[a]
        if ((t >> 1) & 1) ^ c:
            p ^= affine[b]
        assert t.bit_count() & 1
        for x in affine[a]:
            for y in affine[b]:
                p.symmetric_difference_update((x | y,))
    factors = []
    while True:
        pair = next((m for m in sorted(p) if m.bit_count() == 2), None)
        if pair is None:
            break
        i = pair & -pair
        j = pair ^ i
        left = {m ^ i for m in p if m != pair and m & i}
        right = {m ^ j for m in p if m != pair and m & j}
        p = {m for m in p if not m & pair}
        for x in left:
            for y in right:
                p.symmetric_difference_update((x | y,))
        factors.append((right ^ {i}, left ^ {j}))
    new = list(gates)
    def gate(t, a, b):
        new.append((t, a, b))
        return q + len(new) - 1
    def linear(terms):
        atoms = sorted(m.bit_length() - 1 for m in terms if m)
        if not atoms:
            return gate(15 if 0 in terms else 0, 0, 0)
        value = atoms[0]
        for atom in atoms[1:]:
            value = gate(6, value, atom)
        return gate(3, value, value) if 0 in terms else value
    products = [gate(8, linear(a), linear(b)) for a, b in factors]
    for term in products:
        p.symmetric_difference_update((1 << term,))
    out = linear(p)
    if out != q + len(new)-1:
        gate(12, out, out)
    return compact(q, new), len(factors)


def separator(q, gates, labels):
    n = q + len(gates)
    source, sink, infinity = 2*n, 2*n+1, n+1
    graph = [dict() for _ in range(2*n+2)]
    def arc(a, b, capacity):
        graph[a][b] = graph[a].get(b, 0) + capacity
        graph[b].setdefault(a, 0)
    for i in range(n):
        arc(2*i, 2*i+1, 1 if labels[i] is not None else infinity)
        if i < q:
            arc(source, 2*i, infinity)
        else:
            for parent in set(gates[i-q][1:]):
                arc(2*parent+1, 2*i, infinity)
    arc(2*n-1, sink, infinity)
    while True:
        prev = {source: None}
        queue = deque([source])
        while queue and sink not in prev:
            u = queue.popleft()
            for v, cap in graph[u].items():
                if cap > 0 and v not in prev:
                    prev[v] = u
                    queue.append(v)
        if sink not in prev:
            return {i for i in range(n) if 2*i in prev and 2*i+1 not in prev}
        v = sink
        while v != source:
            u = prev[v]
            graph[u][v] -= 1
            graph[v][u] += 1
            v = u


def separator_count(q, gates, rank_cap=12):
    labels = _quadratic_labels(q, gates)
    cut = separator(q, gates, labels)
    representation = _represent(cut, labels, rank_cap)
    if representation is None:
        return None
    basis, descriptors = representation
    r = len(basis)
    spectrum = []
    for y in range(1 << r):
        nodes = [0] * q
        for i, (mask, c) in descriptors.items():
            if i < q:
                nodes[i] = c ^ ((mask & y).bit_count() & 1)
        for i, (table, a, b) in enumerate(gates, q):
            if i in descriptors:
                mask, c = descriptors[i]
                nodes.append(c ^ ((mask & y).bit_count() & 1))
            else:
                nodes.append(table >> (2*nodes[a] + nodes[b]) & 1)
        spectrum.append(nodes[-1])
    width = 1
    while width < len(spectrum):
        for block in range(0, len(spectrum), 2*width):
            for i in range(block, block+width):
                j = i + width
                spectrum[i], spectrum[j] = spectrum[i]+spectrum[j], spectrum[i]-spectrum[j]
        width *= 2
    total = calls = 0
    for s, coefficient in enumerate(spectrum):
        if coefficient:
            p = set()
            for j, polynomial in enumerate(basis):
                if s >> j & 1:
                    p ^= polynomial
            total += coefficient * gauss(p, (1 << q)-1)
            calls += 1
    assert total % (1 << r) == 0
    return dict(count=total >> r, cardinality=len(cut), rank=r, gauss_calls=calls)


def star(q):
    if q < 4:
        raise ValueError("at least four input variables are required")
    gates = []
    def gate(t, a, b):
        gates.append((t, a, b))
        return q + len(gates) - 1
    hub = gate(8, gate(8, 0, 1), 2)
    pieces = [gate(8, hub, i) for i in (*range(3,q), 0, 1, 2)]
    root = pieces[0]
    for piece in pieces[1:]:
        root = gate(6, root, piece)
    return gates
