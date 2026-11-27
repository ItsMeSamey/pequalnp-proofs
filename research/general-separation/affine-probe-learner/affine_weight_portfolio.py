"""Bounded formal symmetry recognition and exact affine coset weight counting."""
from math import comb


def _dependencies(rows):
    pivots, dependencies = {}, []
    for index, word in enumerate(rows):
        coefficients = 1 << index
        while word:
            bit = word.bit_length() - 1
            if bit not in pivots:
                pivots[bit] = word, coefficients
                break
            previous, mask = pivots[bit]
            word ^= previous
            coefficients ^= mask
        if not word:
            dependencies.append(coefficients)
    return dependencies


def _affine(table, left, right):
    zero = table & 1
    lc = ((table >> 2) & 1) ^ zero
    rc = ((table >> 1) & 1) ^ zero
    if not (table.bit_count() & 1):
        if lc and left is None or rc and right is None:
            return None
        return zero ^ (left if lc else 0) ^ (right if rc else 0)
    if left is None or right is None:
        return None
    a, b = left >> 1, right >> 1
    if a and b and a != b:
        return None
    value0 = (table >> (2 * (left & 1) + (right & 1))) & 1
    value1 = (table >> (2 * ((left & 1) ^ bool(a)) + ((right & 1) ^ bool(b)))) & 1
    return (((a | b) << 1) if value0 != value1 else 0) | value0


def _polynomial(form):
    if form < 2:
        return {frozenset()} if form else set()
    return {frozenset((form,))}


def affine_weight_count(q, gates, term_cap=128, state_cap=4096):
    """Return None or an exact count with work metrics. Bit 2*a+b defines a gate."""
    affines = [1 << (i + 1) for i in range(q)]
    polys = [_polynomial(form) for form in affines]
    visits, maximum = 0, 0
    for table, u, v in gates:
        if not 0 <= table < 16 or not 0 <= u < len(affines) or not 0 <= v < len(affines):
            raise ValueError("invalid topological binary gate")
        form = _affine(table, affines[u], affines[v])
        affines.append(form)
        if form is not None:
            poly = _polynomial(form)
        else:
            left, right = polys[u], polys[v]
            zero = table & 1
            lc = ((table >> 2) & 1) ^ zero
            rc = ((table >> 1) & 1) ^ zero
            nonlinear = table.bit_count() & 1
            if left is None and (lc or nonlinear) or right is None and (rc or nonlinear):
                polys.append(None)
                continue
            poly = {frozenset()} if zero else set()
            if lc:
                poly ^= left
            if rc:
                poly ^= right
            if nonlinear:
                pairs = len(left) * len(right)
                if pairs > term_cap * 4:
                    polys.append(None)
                    continue
                visits += pairs
                for first in left:
                    for second in right:
                        poly.symmetric_difference_update((first | second,))
            if len(poly) > term_cap:
                polys.append(None)
                continue
        maximum = max(maximum, len(poly))
        polys.append(poly)
    poly = polys[-1]
    if poly is None:
        return None
    atoms = sorted(set().union(*poly)) if poly else []
    k = len(atoms)
    occupancies = [0] * (k + 1)
    for term in poly:
        occupancies[len(term)] += 1
    levels = []
    for degree, size in enumerate(occupancies):
        if size:
            if size != comb(k, degree):
                return None
            levels.append(degree)
    allowed = [t for t in range(k + 1) if sum(comb(t, j) for j in levels if j <= t) & 1]
    shifts = sum((a & 1) << i for i, a in enumerate(atoms))
    basis = _dependencies([a >> 1 for a in atoms])
    d = len(basis)
    if (1 << d) > state_cap:
        return None
    histogram, current = [0] * (k + 1), 0
    for index in range(1 << d):
        if index:
            current ^= basis[(index & -index).bit_length() - 1]
        histogram[current.bit_count()] += -1 if (current & shifts).bit_count() & 1 else 1
    numerator = 0
    for s, multiplicity in enumerate(histogram):
        if multiplicity:
            for t in allowed:
                coefficient = sum((-1)**j * comb(s, j) * comb(k - s, t - j)
                                  for j in range(max(0, t + s - k), min(s, t) + 1))
                numerator += multiplicity * coefficient
    assert numerator % (1 << d) == 0
    count = (numerator >> d) << (q - k + d)
    return dict(count=count, formal_atoms=k, dual_dimension=d, states=1 << d,
                product_visits=visits, max_terms=maximum)
