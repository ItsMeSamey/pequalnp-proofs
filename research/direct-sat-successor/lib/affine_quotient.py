"""Exact original-input XOR/AND counter by linear image or quadratic quotient.

Budget unit: one enumerated input image or one signed quadratic Gauss sum.
estimate returns a worst-case bound including transformed witness recovery.
"""
from dataclasses import dataclass


def _bits(mask):
    while mask:
        bit = mask & -mask
        yield bit.bit_length() - 1
        mask ^= bit


def _reduce(value, pivots):
    coordinates = 0
    for pivot in sorted(pivots, reverse=True):
        if value >> pivot & 1:
            vector, label = pivots[pivot]
            value ^= vector
            coordinates ^= label
    return value, coordinates


@dataclass
class _Model:
    n: int
    gates: tuple
    output: int
    constants: int
    columns: list
    raw_basis: tuple
    extra: list
    coordinates: list

    @property
    def rho(self):
        return len(self.raw_basis)

    @property
    def tau(self):
        return len(self.extra)


def _model(n, gates, output):
    if not isinstance(n, int) or n < 0:
        raise ValueError("invalid input dimension")
    gates = tuple(gates)
    rows = []
    for j, (left, right) in enumerate(gates):
        for word in (left, right):
            if not isinstance(word, int) or word < 0 or word.bit_length() > n+j+1:
                raise ValueError("invalid or forward gate reference")
            rows.append(word)
    if not isinstance(output, int) or output < 0 or output.bit_length() > n+len(gates)+1:
        raise ValueError("invalid output reference")
    rows.append(output)
    constants = 0
    columns = [0] * (n + len(gates))
    for row, word in enumerate(rows):
        if word & 1:
            constants |= 1 << row
        for column in _bits(word >> 1):
            columns[column] |= 1 << row
    pivots = {}
    for j, col in enumerate(columns[:n]):
        remainder, label = _reduce(col, pivots)
        if remainder:
            pivots[remainder.bit_length()-1] = remainder, label ^ (1 << j)
    raw_basis = tuple(pivots.values())
    extra = []
    coordinates = []
    for col in columns[n:]:
        remainder, label = _reduce(col, pivots)
        if remainder:
            new_coordinate = 1 << (n+len(extra))
            extra.append(remainder)
            pivots[remainder.bit_length()-1] = remainder, new_coordinate
            label ^= new_coordinate
        coordinates.append(label)
    return _Model(n, gates, output, constants, columns, raw_basis, extra, coordinates)


def _bounds(model):
    primal = 1 << model.rho
    # One full count plus at most one zero-branch count at each coordinate.
    quotient = (2 << model.tau) * (1 + model.n + model.tau)
    return primal, quotient


def estimate(n, gates, output):
    return min(_bounds(_model(n, gates, output)))


def _mul(left, right):
    product = set()
    for a in left:
        for b in right:
            product.symmetric_difference_update((a | b,))
    return product


def _quadratics(model):
    rows = [{0} if model.constants >> r & 1 else set()
            for r in range(2*len(model.gates)+1)]
    for j, column in enumerate(model.columns[:model.n] + model.extra):
        for r in _bits(column):
            rows[r].add(1 << j)
    eqs = [{1 << (model.n+j)} for j in range(model.tau)]
    for j, coordinate in enumerate(model.coordinates):
        product = _mul(rows[2*j], rows[2*j+1])
        for eq in _bits(coordinate >> model.n):
            eqs[eq] ^= product
    return eqs, rows[-1], rows


def _restrict(poly, fixed, values):
    result = set()
    for term in poly:
        if not term & (fixed ^ values):
            result.symmetric_difference_update((term & ~fixed,))
    return result


def _gauss(poly, free):
    factor = 1
    while True:
        pair = next((t for t in poly if t.bit_count() == 2), None)
        if pair is None:
            if any(poly):
                return 0
            return (-factor if 0 in poly else factor) << free
        a = pair & -pair
        b = pair ^ a
        left = {t ^ a for t in poly if t != pair and t & a}
        right = {t ^ b for t in poly if t != pair and t & b}
        poly = {t for t in poly if not t & pair} ^ _mul(left, right)
        free -= 2
        factor *= 2


def _count_slice(eqs, output, dimension, fixed, values):
    constraints = [_restrict(p, fixed, values) for p in eqs]
    pin = _restrict(output, fixed, values)
    free = dimension - fixed.bit_count()
    phase = set()
    total = 0
    for step in range(1 << len(eqs)):
        if step:
            phase ^= constraints[(step & -step).bit_length()-1]
        total += _gauss(phase, free) - _gauss(phase ^ pin, free)
    count, remainder = divmod(total, 2 << len(eqs))
    if remainder or count < 0:
        raise ArithmeticError("invalid Fourier count")
    return count


def _physical(model, raw):
    assignment = 1 | raw << 1
    for j, (a, b) in enumerate(model.gates):
        if (a & assignment).bit_count() & (b & assignment).bit_count() & 1:
            assignment |= 1 << (model.n+j+1)
    return (assignment & model.output).bit_count() & 1


def solve(n, gates, output, *, budget):
    model = _model(n, gates, output)
    primal, quotient = _bounds(model)
    use_primal = primal <= quotient
    bound = min(primal, quotient)
    cost = dict(rho=model.rho, tau=model.tau, method="image" if use_primal else "quotient",
                worst_case_units=bound, units=0, gauss_calls=0, masks=0,
                image_patterns=0, count_queries=0)
    if budget < bound:
        return dict(status="skip", cost=cost)
    witness = None
    if use_primal:
        raw = accepted = 0
        for step in range(primal):
            if step:
                raw ^= model.raw_basis[(step & -step).bit_length()-1][1]
            if _physical(model, raw):
                accepted += 1
                if witness is None:
                    witness = raw
        count = accepted << (n-model.rho)
        cost.update(units=primal, image_patterns=primal)
    else:
        eqs, pin, rows = _quadratics(model)
        dimension = n + model.tau
        fixed = values = 0
        count = _count_slice(eqs, pin, dimension, fixed, values)
        queries = 1
        if count:
            for j in range(dimension):
                fixed |= 1 << j
                if _count_slice(eqs, pin, dimension, fixed, values) == 0:
                    values |= 1 << j
                queries += 1
            witness = values & ((1 << n)-1)
            for j, coordinate in enumerate(model.coordinates):
                a, b = rows[2*j:2*j+2]
                if (sum((t & values) == t for t in a) &
                    sum((t & values) == t for t in b) & 1):
                    witness ^= coordinate & ((1 << n)-1)
        masks = queries << model.tau
        cost.update(units=2*masks, gauss_calls=2*masks, masks=masks, count_queries=queries)
    if witness is not None and not _physical(model, witness):
        raise ArithmeticError("reconstructed original witness failed verification")
    result = dict(status="sat" if count else "unsat", count=count, cost=cost)
    if witness is not None:
        result["witness"] = witness
    return result
