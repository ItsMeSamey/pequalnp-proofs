"""Exact binary quadratic-probe counts under a restricted-polar-span budget.

Coordinate i is bit i of the secret.  In Quadratic(constant, linear, pairs),
the coefficient of x_i*x_j for i<j is bit j*(j-1)//2+i of pairs. The constant
is a bit and both masks are nonnegative integers. Public APIs are discover_anchor
and count_histogram. All search branches, counts and signs are deterministic.
"""
from collections.abc import Iterable, Iterator
from dataclasses import dataclass


def _nonnegative(x: int) -> int:
    if not isinstance(x, int) or x < 0:
        raise ValueError("expected a nonnegative integer")
    return x


def _bit(x: int) -> int:
    if not isinstance(x, int) or x not in (0, 1):
        raise ValueError("expected a bit")
    return int(x)


def _dot(a: int, b: int) -> int:
    return (a & b).bit_count() & 1


def _indices(mask: int) -> Iterator[int]:
    while mask:
        bit = mask & -mask
        yield bit.bit_length() - 1
        mask ^= bit


@dataclass(frozen=True)
class Quadratic:
    constant: int
    linear: int
    pairs: int

    def __post_init__(self):
        _bit(self.constant)
        _nonnegative(self.linear)
        _nonnegative(self.pairs)

    def __xor__(self, other: "Quadratic") -> "Quadratic":
        return Quadratic(self.constant ^ other.constant, self.linear ^ other.linear,
                         self.pairs ^ other.pairs)

    def evaluate(self, seed: int) -> int:
        """Evaluate on a packed seed (omitted high coordinates are zero)."""
        _nonnegative(seed)
        result = self.constant ^ _dot(seed, self.linear)
        for j in _indices(seed):
            column = self.pairs >> (j * (j - 1) // 2)
            result ^= _dot(column & ((1 << j) - 1), seed)
        return result


def _validate_query(h: int, query: Quadratic) -> None:
    if not isinstance(query, Quadratic):
        raise TypeError("expected Quadratic(constant, linear, pairs)")
    if query.linear.bit_length() > h or query.pairs.bit_length() > h * (h - 1) // 2:
        raise ValueError("quadratic uses an out-of-range coordinate")


def _polar_rows(h: int, pairs: int) -> tuple[int, ...]:
    rows = [0] * h
    for j in range(h):
        column = (pairs >> (j * (j - 1) // 2)) & ((1 << j) - 1)
        rows[j] |= column
        for i in _indices(column):
            rows[i] |= 1 << j
    return tuple(rows)


def _contract(rows: tuple[int, ...], x: int) -> int:
    result = 0
    for i in _indices(x):
        result ^= rows[i]
    return result


def _pull_polar(rows: tuple[int, ...], directions: tuple[int, ...]) -> int:
    pairs = 0
    for j, v in enumerate(directions):
        image = _contract(rows, v)
        column = sum(_dot(image, directions[i]) << i for i in range(j))
        pairs |= column << (j * (j - 1) // 2)
    return pairs


def _pull(query: Quadratic, old_dim: int, origin: int,
          directions: tuple[int, ...]) -> Quadratic:
    constant = query.evaluate(origin)
    linear = sum((query.evaluate(origin ^ v) ^ constant) << i
                 for i, v in enumerate(directions))
    return Quadratic(constant, linear,
                     _pull_polar(_polar_rows(old_dim, query.pairs), directions))


def _insert(pivots: dict[int, int], row: int) -> bool:
    while row:
        pivot = row.bit_length() - 1
        if pivot not in pivots:
            pivots[pivot] = row
            return True
        row ^= pivots[pivot]
    return False


def _space(dim: int, equations: Iterable[tuple[int, int]]):
    """Return origin, kernel basis, and its identity-column indices, or None."""
    pivots = {}
    for row, bit in equations:
        while row:
            j = row.bit_length() - 1
            if j not in pivots:
                pivots[j] = row, bit
                break
            other, value = pivots[j]
            row ^= other
            bit ^= value
        else:
            if bit:
                return None
    ordered = sorted(pivots.items())

    def solve(free_bits: int, homogeneous: bool) -> int:
        x = free_bits
        for j, (row, bit) in ordered:
            if _dot(row, x) ^ (0 if homogeneous else bit):
                x |= 1 << j
        return x

    free = tuple(j for j in range(dim) if j not in pivots)
    return solve(0, False), tuple(solve(1 << j, True) for j in free), free


def _combinations(rows: tuple[int, ...]) -> Iterator[int]:
    """Nonzero index combinations in Gray-code order, returned as XORs."""
    value = 0
    for step in range(1, 1 << len(rows)):
        value ^= rows[(step & -step).bit_length() - 1]
        yield value


def discover_anchor(h: int, k: int, r: int,
                    stored_queries: Iterable[Quadratic]) -> tuple[int, ...] | None:
    """Find independent ambient masks W of size <=k meeting the polar-span bound.

    Only the stored queries participate. Return None when no such anchor exists.
    """
    for parameter in (h, k, r):
        _nonnegative(parameter)
    polars = []
    for query in stored_queries:
        _validate_query(h, query)
        polars.append(_polar_rows(h, query.pairs))
    stack = [()]
    while stack:
        anchor = stack.pop()
        _, kernel, free = _space(h, ((w, 0) for w in anchor))
        restricted = {}
        for rows in polars:
            _insert(restricted, _pull_polar(rows, kernel))
            if len(restricted) > r:
                break
        if len(restricted) <= r:
            return anchor
        remaining = k - len(anchor)
        if not remaining:
            continue
        tried = set()
        for polar in _combinations(tuple(restricted.values())):
            image = {}
            for row in _polar_rows(len(kernel), polar):
                _insert(image, row)
            rank = len(image)
            if rank > 2 * remaining:
                continue
            # For this individual nonzero alternating form choose u+1
            # independent contraction functionals, where its rank is 2u.
            if not rank or rank % 2:
                raise AssertionError("invalid restricted alternating form")
            selected = tuple(image.values())[:rank // 2 + 1]
            for functional in _combinations(selected):
                if functional in tried:
                    continue
                tried.add(functional)
                # Kernel basis vector i projects to unit i on free columns.
                # The coordinate functional lifts literally on those columns.
                lift = sum(1 << free[i] for i in _indices(functional))
                stack.append((*anchor, lift))
    return None


def _gauss(dim: int, query: Quadratic) -> int:
    """Sum (-1)**Q over the dim-bit cube using symplectic splitting."""
    polar = _polar_rows(dim, query.pairs)
    basis = [1 << i for i in range(dim)]
    pairs = 0
    sign = query.constant
    while basis:
        pair = None
        for i, e in enumerate(basis):
            image = _contract(polar, e)
            j = next((j for j in range(i + 1, len(basis)) if _dot(image, basis[j])), None)
            if j is not None:
                pair = i, j
                break
        if pair is None:
            if any(query.evaluate(v) ^ query.constant for v in basis):
                return 0
            break
        i, j = pair
        e, f = basis[i], basis[j]
        be, bf = _contract(polar, e), _contract(polar, f)
        sign ^= (query.evaluate(e) ^ query.constant) & (query.evaluate(f) ^ query.constant)
        basis = [v ^ (e if _dot(v, bf) else 0) ^ (f if _dot(v, be) else 0)
                 for n, v in enumerate(basis) if n not in pair]
        pairs += 1
    total = 1 << (pairs + len(basis))
    return -total if sign else total


def _count_cell(dim: int, equations: Iterable[Quadratic]) -> int:
    pivots = {}
    affine = []
    for eq in equations:
        while eq.pairs:
            j = eq.pairs.bit_length() - 1
            if j not in pivots:
                pivots[j] = eq
                break
            eq = eq ^ pivots[j]
        else:
            affine.append((eq.linear, eq.constant))
    space = _space(dim, affine)
    if space is None:
        return 0
    origin, basis, _ = space
    remaining = [_pull(eq, dim, origin, basis) for eq in pivots.values()]
    value = Quadratic(0, 0, 0)
    signed_sum = 1 << len(basis)
    for step in range(1, 1 << len(remaining)):
        value = value ^ remaining[(step & -step).bit_length() - 1]
        signed_sum += _gauss(len(basis), value)
    return signed_sum // (1 << len(remaining))


def count_histogram(h: int, k: int, r: int, stored: Iterable[tuple[Quadratic, int]],
                    current: Quadratic) -> tuple[int, int] | None:
    """Count consistent seeds producing current labels zero and one.

    stored contains (quadratic, observed bit) pairs. None means the stored
    polars have no eligible anchor. Contradictory stored observations instead
    return (0,0) when an eligible anchor exists. Current need not satisfy the
    stored span promise. For online use, predict one iff count1 > count0 and
    retain an observation only on a mistake; a failed discovery can default to zero.
    """
    for parameter in (h, k, r):
        _nonnegative(parameter)
    _validate_query(h, current)
    history = [(row, _bit(label)) for row, label in stored]
    anchor = discover_anchor(h, k, r, (row for row, _ in history))
    if anchor is None:
        return None
    totals = [0, 0]
    for values in range(1 << len(anchor)):
        origin, kernel, _ = _space(h, ((w, (values >> i) & 1)
                                       for i, w in enumerate(anchor)))
        equations = [_pull(row, h, origin, kernel) ^ Quadratic(label, 0, 0)
                     for row, label in history]
        test = _pull(current, h, origin, kernel)
        for bit in (0, 1):
            totals[bit] += _count_cell(len(kernel), [*equations, test ^ Quadratic(bit, 0, 0)])
    return totals[0], totals[1]
