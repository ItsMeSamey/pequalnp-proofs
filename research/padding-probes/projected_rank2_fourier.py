"""Private-pair specialization of syndrome_fourier.fourier_count_witness."""
from affine_relation import solve_equations


def count_witness(d, flats, *, codimension_cap=None):
    """Return (count, seed, metrics); count=None means the rank cap was exceeded."""
    if type(d) is not int or d < 0:
        raise ValueError("invalid seed dimension")
    if codimension_cap is not None and (type(codimension_cap) is not int or codimension_cap < 0):
        raise ValueError("invalid codimension cap")
    normals = []
    offsets = 0
    for flat in flats:
        first, second = tuple(flat)
        if first[0] == second[0]:
            raise ValueError("dependent flat normals")
        for mask, rhs in (first, second):
            if type(mask) is not int or not 0 < mask < 1 << d or rhs not in (0, 1):
                raise ValueError("invalid rank-two equation")
            # Flag one precisely when this equation holds.
            offsets |= (1 ^ rhs) << len(normals)
            normals.append(mask)

    basis = {}
    checks = []
    for i, normal in enumerate(normals):
        relation = 1 << i
        while normal:
            pivot = normal.bit_length() - 1
            if pivot not in basis:
                basis[pivot] = normal, relation
                break
            row, combination = basis[pivot]
            normal ^= row
            relation ^= combination
        if not normal:
            checks.append(relation)
    rank = len(basis)
    r = len(checks)
    metrics = dict(normal_rank=rank, syndrome_rank=r, pairs=len(normals)//2,
                   fiber_dimension=d-rank, count_calls=0, character_terms=0)
    if codimension_cap is not None and r > codimension_cap:
        return None, None, metrics
    columns = [0] * len(normals)
    target = 0
    for j, check in enumerate(checks):
        target |= ((check & offsets).bit_count() % 2) << j
        remaining = check
        while remaining:
            bit = remaining & -remaining
            columns[bit.bit_length()-1] |= 1 << j
            remaining ^= bit

    def count_suffix(start, wanted):
        numerator = 0
        metrics["count_calls"] += 1
        metrics["character_terms"] += 1 << r
        for character in range(1 << r):
            term = -1 if (character & wanted).bit_count() % 2 else 1
            for i in range(start, len(columns), 2):
                left = (character & columns[i]).bit_count() % 2
                right = (character & columns[i+1]).bit_count() % 2
                # Allowed pair values are 00, 10 and 01.
                term *= 3 - 2*(left + right)
            numerator += term
        return numerator // (1 << r)

    legal = count_suffix(0, target)
    if not legal:
        return 0, None, metrics
    flags = 0
    residual = target
    for i in range(0, len(columns), 2):
        if count_suffix(i+2, residual):
            continue
        if count_suffix(i+2, residual ^ columns[i]):
            flags |= 1 << i
            residual ^= columns[i]
        else:
            flags |= 1 << (i+1)
            residual ^= columns[i+1]
    values = flags ^ offsets
    seed = solve_equations(d, ((row, (values >> i) & 1) for i, row in enumerate(normals)))
    if residual or seed is None:
        raise ArithmeticError("invalid syndrome witness")
    return legal << (d-rank), seed, metrics
