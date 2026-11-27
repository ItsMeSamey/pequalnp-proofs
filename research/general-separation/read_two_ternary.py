"""Evaluate a positive read-two CNF's multilinear extension at a point of F3."""


def evaluate(clauses, point):
    """Use zero-based variable indices. Repeated literals within a clause collapse."""
    if not all(type(value) is int and 0 <= value < 3 for value in point):
        raise ValueError("expected field entries 0, 1, or 2")
    incidences = [[] for _ in point]
    count = 0
    for index, clause in enumerate(clauses):
        seen = set()
        for variable in clause:
            if type(variable) is not int or not 0 <= variable < len(point):
                raise ValueError("invalid variable index")
            if variable not in seen:
                seen.add(variable)
                incidents = incidences[variable]
                incidents.append(index)
                if len(incidents) > 2:
                    raise ValueError("variable belongs to more than two clauses")
        count = index + 1

    active = (1 << count) - 1
    for value, incidents in zip(point, incidences):
        if value == 1:
            for clause in incidents:
                active &= ~(1 << clause)

    linear = active
    edges = [0] * count
    for value, incidents in zip(point, incidences):
        if value != 2:
            continue
        endpoints = [i for i in incidents if active & (1 << i)]
        for i in endpoints:
            linear ^= 1 << i
        if len(endpoints) == 2:
            i, j = endpoints
            edges[i] ^= 1 << j
            edges[j] ^= 1 << i

    scalar = 1
    while True:
        i = next((k for k, neighbors in enumerate(edges) if neighbors), None)
        if i is None:
            break
        j_bit = edges[i] & -edges[i]
        j = j_bit.bit_length() - 1
        i_bit = 1 << i
        removed = i_bit | j_bit
        active &= ~removed
        a = edges[i] & active
        b = edges[j] & active
        a0 = bool(linear & i_bit)
        b0 = bool(linear & j_bit)
        # Sum over i,j replaces i*j+i*A+j*B by A*B with factor two.
        scalar = scalar * (1 if a0 and b0 else 2) % 3
        linear &= active
        linear ^= a & b
        if a0:
            linear ^= b
        if b0:
            linear ^= a
        edges[i] = 0
        edges[j] = 0
        for k in range(count):
            k_bit = 1 << k
            neighbors = edges[k] & active
            if a & k_bit:
                neighbors ^= b
            if b & k_bit:
                neighbors ^= a
            edges[k] = neighbors

    if linear:
        return 0
    return scalar * pow(2, active.bit_count(), 3) % 3
