"""Low bits of the signed gap for disjoint cubic triples plus a quadratic drift.

The solver uses the sibling module original_dag_quadratic.gauss for exact binary
quadratic sign sums. Its time is FPT in the requested precision and the maximum
degree of the triple interaction graph. Space is polynomial in the input size.
"""

from original_dag_quadratic import gauss


def subsets(mask):
    current = mask
    while True:
        yield current
        if current == 0:
            return
        current = (current - 1) & mask


def vertices(mask):
    while mask:
        bit = mask & -mask
        yield bit.bit_length() - 1
        mask ^= bit


def connected_sets(adjacency, limit):
    """Enumerate by reverse search, deleting the largest removable vertex."""
    def neighbors(mask):
        result = 0
        for vertex in vertices(mask):
            result |= adjacency[vertex]
        return result

    def connected(mask):
        reached = mask & -mask
        while True:
            expanded = reached | (neighbors(reached) & mask)
            if expanded == reached:
                return reached == mask
            reached = expanded

    def parent(mask):
        candidates = mask
        while candidates:
            bit = 1 << (candidates.bit_length() - 1)
            if connected(mask ^ bit):
                return mask ^ bit
            candidates ^= bit
        raise AssertionError("connected set has no removable vertex")

    def children(mask):
        if mask.bit_count() < limit:
            for vertex in vertices(neighbors(mask) & ~mask):
                child = mask | (1 << vertex)
                if parent(child) == mask:
                    yield child

    if limit:
        for vertex in range(len(adjacency)):
            root = 1 << vertex
            yield root
            stack = [children(root)]
            while stack:
                child = next(stack[-1], None)
                if child is None:
                    stack.pop()
                else:
                    yield child
                    stack.append(children(child))


def lowbits(m, monomials, k):
    """Count for m consecutive triples and a quadratic ANF of monomial masks.

    Let Z be the signed sum and Q(1) be the drift at the all-ones assignment.
    Both residue fields are reduced modulo 2**k. The existing 'residue' field
    gives Z / ((-2)**m * (-1)**Q(1)). 'gap_div_2m_mod' gives Z / 2**m.
    A repeated monomial cancels over GF(2). Mask zero denotes the constant.
    """
    if m < 0 or k < 0:
        raise ValueError("negative size")
    drift = set()
    for term in monomials:
        if term < 0 or term.bit_count() > 2 or term >> (3 * m):
            raise ValueError("invalid quadratic monomial")
        drift.symmetric_difference_update((term,))

    drift_at_one = len(drift) % 2
    adjacency = [0] * m
    for term in drift:
        if term.bit_count() == 2:
            left, right = [index // 3 for index in vertices(term)]
            if left != right:
                adjacency[left] |= 1 << right
                adjacency[right] |= 1 << left

    def omission_weight(omitted):
        free = sum(7 << (3 * vertex) for vertex in vertices(omitted))
        restricted = {0} if drift_at_one else set()
        for term in drift:
            restricted.symmetric_difference_update((term & free,))
        size = omitted.bit_count()
        weight, remainder = divmod(gauss(restricted, free), (-2) ** size)
        assert remainder == 0 and weight % (1 << ((size + 1) // 2)) == 0
        return weight

    # For each connected set sum its subset-Mobius contribution to zP'/P.
    limit = min(m, max(0, 2 * k - 2))
    log_derivative = [0] * (limit + 1)
    visited = 0
    for cluster in connected_sets(adjacency, limit):
        visited += 1
        for induced in subsets(cluster):
            polynomial = [0] * (induced.bit_count() + 1)
            for omitted in subsets(induced):
                polynomial[omitted.bit_count()] += omission_weight(omitted)
            local = [0] * (limit + 1)
            for degree in range(1, limit + 1):
                rhs = degree * polynomial[degree] if degree < len(polynomial) else 0
                bound = min(degree, len(polynomial) - 1)
                correction = sum(polynomial[i] * local[degree - i] for i in range(1, bound + 1))
                local[degree] = rhs - correction
            sign = (-1) ** (cluster ^ induced).bit_count()
            for degree in range(cluster.bit_count(), limit + 1):
                log_derivative[degree] += sign * local[degree]

    coefficients = [1]
    for degree in range(1, limit + 1):
        numerator = sum(log_derivative[i] * coefficients[degree - i] for i in range(1, degree + 1))
        coefficient, remainder = divmod(numerator, degree)
        assert remainder == 0
        coefficients.append(coefficient)

    modulus = 1 << k
    centered = sum(coefficients) % modulus
    orientation = (-1) ** (m + drift_at_one)
    return {
        "residue": centered,
        "gap_div_2m_mod": orientation * centered % modulus,
        "bits": k,
        "cutoff": limit,
        "connected": visited,
        "degree": max((mask.bit_count() for mask in adjacency), default=0),
        "q_at_one": drift_at_one,
    }


def selftest():
    from random import Random

    rng = Random(788)
    cases = 0
    for m in range(5):
        variables = range(3 * m)
        possible = [0] + [1 << i for i in variables]
        possible.extend((1 << j) | (1 << i) for i in variables for j in range(i))
        for _ in range(7):
            drift = {term for term in possible if rng.randrange(4) == 0}
            phase = drift | {7 << (3 * i) for i in range(m)}
            raw = 0
            for x in range(1 << (3 * m)):
                parity = sum((term & x) == term for term in phase) % 2
                raw += (-1) ** parity
            centered, rem = divmod(raw, (-2) ** m * (-1) ** len(drift))
            assert rem == 0
            gap_div_2m, rem = divmod(raw, 1 << m)
            assert rem == 0
            for k in range(5):
                result = lowbits(m, drift, k)
                assert result["residue"] == centered % (1 << k)
                assert result["gap_div_2m_mod"] == gap_div_2m % (1 << k)
            cases += 1

    # Independent transfer for a 72-block path, integrating the partners locally.
    m = 72
    drift = {(1 << (3 * i)) | (1 << (3 * i + 3)) for i in range(m - 1)}
    result = lowbits(m, drift, 3)
    assert result["connected"] == sum(m - size + 1 for size in range(1, 5))
    zero, one = 4, 2
    for _ in range(1, m):
        zero, one = 4 * (zero + one), 2 * (zero - one)
    raw = zero + one
    assert raw % (1 << m) == 0
    assert result["gap_div_2m_mod"] == (raw >> m) % 8
    assert result["residue"] == raw // ((-2) ** m * (-1) ** len(drift)) % 8
    print(cases, "raw phase systems at k=0..4; 72-block path", result)


if __name__ == "__main__":
    selftest()
