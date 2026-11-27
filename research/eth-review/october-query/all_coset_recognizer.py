"""Find a common direction space with quadratic restriction on every coset.

Each ANF is an iterable of monomial masks. Repetitions cancel mod two.
Directions in the result are given in the original coordinates.
"""
from itertools import combinations


def indices(mask):
    while mask:
        bit = mask & -mask
        yield bit.bit_length() - 1
        mask ^= bit


def combine(mask, vectors):
    result = 0
    for i in indices(mask):
        result ^= vectors[i]
    return result


def span(vectors, nonzero=False):
    for mask in range(int(nonzero), 1 << len(vectors)):
        yield combine(mask, vectors)


def toggle(terms, mask):
    if mask in terms:
        terms.remove(mask)
    else:
        terms.add(mask)


def pivots(vectors):
    echelon = {}
    selected = []
    for position, row in enumerate(vectors):
        while row:
            j = row.bit_length() - 1
            if j not in echelon:
                echelon[j] = row
                selected.append(position)
                break
            row ^= echelon[j]
    return tuple(echelon.values()), selected


def restrict(poly, forms, offset):
    result = set()
    for monomial in poly:
        product = {0}
        for raw in indices(monomial):
            terms = product.copy() if offset & (1 << raw) else set()
            for term in product:
                for coord in indices(forms[raw]):
                    toggle(terms, term | (1 << coord))
            product = terms
            if not product:
                break
        result.symmetric_difference_update(product)
    return result


def cubic_witness(polynomials, n, basis, complement):
    forms = [sum(((v >> raw) & 1) << i for i, v in enumerate(basis)) for raw in range(n)]
    for offset in span(complement):
        for poly in polynomials:
            terms = restrict(poly, forms, offset)
            maximal = max(terms, key=int.bit_count, default=0)
            if maximal.bit_count() < 3:
                continue
            differentiate = sum(1 << i for i in list(indices(maximal))[3:])
            return [tuple(indices(m ^ differentiate)) for m in terms
                    if (m & differentiate) == differentiate
                    and (m ^ differentiate).bit_count() == 3]
    return None


def normals(dim, budget, triples):
    # Adapt the cubic-width contraction branching to return physical hyperplanes.
    pairs = list(combinations(range(dim), 2))
    positions = {pair: j for j, pair in enumerate(pairs)}
    slices = [0] * dim
    for i, j, k in triples:
        slices[i] ^= 1 << positions[j, k]
        slices[j] ^= 1 << positions[i, k]
        slices[k] ^= 1 << positions[i, j]
    _, selected = pivots(slices)
    if len(selected) <= budget:
        # The transpose image is the annihilator of the radical.
        image, _ = pivots(sum(((row >> j) & 1) << i for i, row in enumerate(slices))
                          for j in range(len(pairs)))
        yield from span(image, nonzero=True)
        return
    trial = tuple(1 << i for i in selected[:budget + 1])
    for x in span(trial, nonzero=True):
        rows = [0] * dim
        for pos in indices(combine(x, slices)):
            i, j = pairs[pos]
            rows[i] |= 1 << j
            rows[j] |= 1 << i
        image, _ = pivots(rows)
        if 0 < len(image) <= 2 * budget:
            yield from span(image, nonzero=True)


def recognize(n, polynomials, t):
    """Return a basis of codimension at most t, or None if no subspace works."""
    if not isinstance(n, int) or not isinstance(t, int) or min(n, t) < 0:
        raise ValueError("n and t must be nonnegative integers")
    normalized = []
    for terms in polynomials:
        poly = set()
        for monomial in terms:
            if not isinstance(monomial, int) or monomial < 0 or monomial.bit_length() > n:
                raise ValueError("monomial outside declared coordinates")
            toggle(poly, monomial)
        normalized.append(poly)
    # Stream offsets and children, retaining only a path of depth at most n.
    stack = [(tuple(1 << i for i in range(n)), (), min(n, t), None)]
    while stack:
        basis, complement, budget, candidates = stack[-1]
        if candidates is None:
            if len(basis) <= 2:
                return basis
            triples = cubic_witness(normalized, n, basis, complement)
            if triples is None:
                return basis
            if budget == 0:
                stack.pop()
                continue
            candidates = normals(len(basis), budget, triples)
            stack[-1] = (basis, complement, budget, candidates)
        normal = next(candidates, None)
        if normal is None:
            stack.pop()
            continue
        pivot = (normal & -normal).bit_length() - 1
        outside = basis[pivot]
        child = tuple(v ^ outside if (normal >> i) & 1 else v
                      for i, v in enumerate(basis) if i != pivot)
        stack.append((child, complement + (outside,), budget - 1, None))
    return None
