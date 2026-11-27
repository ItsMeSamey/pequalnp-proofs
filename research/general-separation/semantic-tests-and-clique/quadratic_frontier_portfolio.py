"""Exact counts through an automatically selected low-rank quadratic frontier."""
from original_dag_quadratic import gauss


def _quadratic_labels(q, gates):
    labels = [{1 << i} for i in range(q)]
    for table, u, v in gates:
        zero = table & 1
        xflag = ((table >> 2) & 1) ^ zero
        yflag = ((table >> 1) & 1) ^ zero
        product = table.bit_count() & 1
        a, b = labels[u], labels[v]
        if a is None and (xflag or product) or b is None and (yflag or product):
            labels.append(None)
            continue
        current = {0} if zero else set()
        if xflag:
            current ^= a
        if yflag:
            current ^= b
        if product:
            for s in a:
                for t in b:
                    current.symmetric_difference_update((s | t,))
        labels.append(current if all(term.bit_count() <= 2 for term in current) else None)
    return labels


def _represent(frontier, labels, cap):
    basis, pivots, expressions = [], {}, {}
    for gate in sorted(frontier):
        p = labels[gate]
        if p is None:
            return None
        residual = p - {0}
        combination = 0
        while residual:
            lead = max(residual)
            if lead not in pivots:
                if len(basis) == cap:
                    return None
                index = len(basis)
                pivots[lead] = index
                basis.append(residual.copy())
                combination ^= 1 << index
                break
            index = pivots[lead]
            residual ^= basis[index]
            combination ^= 1 << index
        expressions[gate] = combination, int(0 in p)
    return basis, expressions


def quadratic_frontier_count(q, gates, rank_cap=12):
    """Frontier search uses the original DAG; no primary truth table is required."""
    labels = _quadratic_labels(q, gates)
    output = q + len(gates) - 1
    frontier = {output}
    best, needed = None, set()
    for cut in range(len(gates), -1, -1):
        cap = rank_cap if best is None else min(rank_cap, len(best[1]) - 1)
        if cap >= 0:
            state = _represent(frontier, labels, cap)
            if state is not None:
                best = cut, *state
        if cut:
            node = q + cut - 1
            if node in frontier:
                needed.add(node)
                frontier.remove(node)
                frontier.update(gates[cut - 1][1:])
    if best is None:
        return None
    cut, quadratic_basis, coordinate_map = best
    r = len(quadratic_basis)
    values = []
    for y in range(1 << r):
        computed = {node: shift ^ ((mask & y).bit_count() & 1)
                    for node, (mask, shift) in coordinate_map.items()}
        for i in range(cut, len(gates)):
            if q + i in needed:
                table, u, v = gates[i]
                computed[q + i] = (table >> (2 * computed[u] + computed[v])) & 1
        values.append(computed[output])
    size = 1
    while size < len(values):
        for base in range(0, len(values), size * 2):
            for j in range(size):
                p, s = base + j, base + j + size
                values[p], values[s] = values[p] + values[s], values[p] - values[s]
        size *= 2
    total = nonzero = 0
    for mask, coefficient in enumerate(values):
        if coefficient:
            p = set()
            for i, term in enumerate(quadratic_basis):
                if mask >> i & 1:
                    p ^= term
            total += coefficient * gauss(p, (1 << q) - 1)
            nonzero += 1
    assert total % (1 << r) == 0
    return dict(count=total >> r, cut=cut, rank=r, table_entries=1 << r, gauss_calls=nonzero)


def coupled_quadratics(q):
    if q % 4:
        raise ValueError("a multiple of four input bits is required")
    gates = []
    def gate(op, a, b):
        gates.append((op, a, b))
        return q + len(gates) - 1
    def parity(items):
        result = items[0]
        for item in items[1:]:
            result = gate(6, result, item)
        return result
    n = q // 2
    first = parity([gate(8, j, n + j) for j in range(n)])
    pairs = [(j+i, n+j+k) for j in range(0,n,2) for i,k in ((0,1),(1,0),(1,1))]
    second = parity([gate(8, u, v) for u,v in pairs])
    gate(8, first, second)
    return gates
