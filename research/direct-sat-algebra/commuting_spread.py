"""A raw binary square pencil with certified field of multiplication ratios."""
from quadratic_target import apply_basis, insert, reduce_vector


def inverse_columns(cols):
    rows = {}
    for i, x in enumerate(cols):
        if not insert(x, 1 << i, rows):
            return None
    return [reduce_vector(1 << i, rows)[1] for i in range(len(cols))]


def compose(left, right):
    return [apply_basis(left, x) for x in right]


def kernel_columns(cols):
    rows, kernel = {}, []
    for j, col in enumerate(cols):
        residual, adjustment = reduce_vector(col, rows)
        if residual:
            insert(col, 1 << j, rows)
        else:
            kernel.append(adjustment ^ (1 << j))
    return kernel


def solve(matrices, drift):
    """Return (input slope mask, inverse columns) or None if inconclusive."""
    d = len(drift)
    if not d or len(matrices) != d or any(len(m) != d for m in matrices):
        raise ValueError("expected d homogeneous d by d matrices")
    if any(x < 0 or x >= 1 << d for m in [*matrices, drift] for x in m):
        raise ValueError("invalid packed binary column")
    inv = inverse_columns(matrices[0])
    if inv is None:
        return None
    ratios = [compose(inv, m) for m in matrices]
    a = compose(inv, drift)

    def pack(cols):
        return sum(x << (d*j) for j, x in enumerate(cols))

    packed = [pack(m) for m in ratios]
    rows = {}
    if not all(insert(x, 1 << i, rows) for i, x in enumerate(packed)):
        return None
    squares = []
    for i, x in enumerate(ratios):
        for j in range(i + 1):
            prod = compose(x, ratios[j])
            if i != j and prod != compose(ratios[j], x):
                return None
            remainder, coords = reduce_vector(pack(prod), rows)
            if remainder:
                return None
            if i == j:
                squares.append(coords)
    if kernel_columns(squares) or len(kernel_columns(
            [x ^ (1 << i) for i, x in enumerate(squares)])) != 1:
        return None
    commutators = [pack(compose(x, a)) ^ pack(compose(a, x)) for x in ratios]
    scalars = kernel_columns(commutators)
    n = d // len(scalars)
    for code in range(min(1 << len(scalars), n+1)):
        slope = apply_basis(scalars, code)
        packed_matrix = pack(drift) ^ apply_basis([pack(m) for m in matrices], slope)
        cols = [(packed_matrix >> (j*d)) & ((1 << d)-1) for j in range(d)]
        inv = inverse_columns(cols)
        if inv is not None:
            return slope, inv
    return None
