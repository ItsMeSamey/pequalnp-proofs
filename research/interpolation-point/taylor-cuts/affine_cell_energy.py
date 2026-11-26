"""Exact Walsh energy and a minimal linear interface for weighted affine cells.

Masks are little-endian binary vectors. Equations are (mask, bit) pairs.
A cell term is (signed exact weight, equations). The unnormalized Walsh
transform is sum_x f(x) (-1)^(s dot x). Arithmetic supports Fraction.
"""
from dataclasses import dataclass
from fractions import Fraction


def dot(a, b):
    return (a & b).bit_count() & 1


def solve(n, equations):
    """Return a particular point and kernel basis, or None on inconsistency."""
    pivots = {}
    inconsistent = False
    for mask, bit in equations:
        if not isinstance(mask, int) or not 0 <= mask < 1 << n or bit not in (0, 1):
            raise ValueError("invalid binary equation")
        while mask:
            pivot = mask.bit_length() - 1
            if pivot not in pivots:
                pivots[pivot] = (mask, bit)
                break
            previous, rhs = pivots[pivot]
            mask ^= previous
            bit ^= rhs
        else:
            inconsistent |= bool(bit)
    if inconsistent:
        return None
    def extend(free, homogeneous):
        result = free
        for pivot in sorted(pivots):
            mask, bit = pivots[pivot]
            if dot(mask, result) ^ (0 if homogeneous else bit):
                result |= 1 << pivot
        return result
    kernel = tuple(extend(1 << i, True) for i in range(n) if i not in pivots)
    return extend(0, False), kernel


@dataclass(frozen=True)
class Pair:
    coefficient: Fraction
    phase: int
    equations: tuple


class AffineCellEnergy:
    def __init__(self, n, terms):
        if not isinstance(n, int) or n < 0:
            raise ValueError("invalid dimension")
        self.n = n
        records = []
        for weight, equations in terms:
            if not isinstance(weight, (int, Fraction)):
                raise ValueError("use integer or rational weights")
            cell = solve(n, equations)
            if cell is not None and weight:
                point, kernel = cell
                records.append((weight * (1 << len(kernel)), point,
                                tuple((v, 0) for v in kernel)))
        self.pairs = []
        for i, (weight, point, equations) in enumerate(records):
            for j in range(i + 1):
                other, other_point, other_eq = records[j]
                self.pairs.append(Pair(weight * other * (1 if i == j else 2),
                                       point ^ other_point, equations + other_eq))

    def energy(self, frequency_cell=()):
        """Return sum of squared Walsh coefficients on the frequency cell."""
        query = tuple(frequency_cell)
        if solve(self.n, query) is None:
            return 0
        total = 0
        for pair in self.pairs:
            region = solve(self.n, query + pair.equations)
            if region is None:
                continue
            point, kernel = region
            if any(dot(pair.phase, direction) for direction in kernel):
                continue
            value = pair.coefficient * (1 << len(kernel))
            total += -value if dot(pair.phase, point) else value
        return total

    def interface(self):
        """Return independent frequencies spanning all nonzero coefficients."""
        basis = []
        while True:
            _, orthogonal = solve(self.n, ((v, 0) for v in basis))
            query = next(([(v, 1)] for v in orthogonal if self.energy([(v, 1)])), None)
            if query is None:
                return tuple(basis)
            point = 0
            for i in range(self.n):
                eq = (1 << i, 0)
                bit = int(not self.energy(query + [eq]))
                query.append((1 << i, bit))
                point |= bit << i
            basis.append(point)
