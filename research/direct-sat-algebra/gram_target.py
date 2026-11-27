"""One-sided rational moment certificates for explicit binary quadratic fibers."""

from dataclasses import dataclass
from fractions import Fraction
from collections import defaultdict
from math import gcd, lcm
from quadratic_image import ZERO, add, bits, evaluate, gauss, normalize, parity


@dataclass(frozen=True)
class GramResult:
    status: str
    reason: str
    phase_evals: int
    dictionary: tuple
    annihilator: tuple | None = None
    count_upper: int | None = None
    energy: Fraction | None = None
    count: int | None = None
    witness: int | None = None


def _solve(gram, target_signs):
    """Solve G z = v or obtain w in ker G with w.v != 0."""
    size = len(gram)
    rows = [[Fraction(x) for x in row + [target_signs[i]]] for i, row in enumerate(gram)]
    pivots = []
    for j in range(size):
        rank = len(pivots)
        i = next((i for i in range(rank, size) if rows[i][j]), None)
        if i is None:
            continue
        rows[rank], rows[i] = rows[i], rows[rank]
        pivot = rows[rank][j]
        rows[rank] = [v / pivot for v in rows[rank]]
        for i in range(size):
            if i != rank and rows[i][j]:
                scale = rows[i][j]
                rows[i] = [v - scale * w for v, w in zip(rows[i], rows[rank])]
        pivots.append(j)
    solution = [Fraction(0)] * size
    if all(not row[-1] for row in rows[len(pivots):]):
        for i, j in enumerate(pivots):
            solution[j] = rows[i][-1]
        return solution, None
    # Symmetry turns a right-null relation into an annihilating row relation.
    for free in sorted(set(range(size)) - set(pivots)):
        vector = [Fraction(0)] * size
        vector[free] = 1
        for i, j in enumerate(pivots):
            vector[j] = -rows[i][free]
        if sum(a * b for a, b in zip(vector, target_signs)):
            scale = lcm(*(a.denominator for a in vector))
            integers = [int(a * scale) for a in vector]
            divisor = gcd(*integers)
            return None, tuple(a // divisor for a in integers)
    raise ArithmeticError("missing annihilating character relation")


class _BudgetExhausted(Exception):
    pass


def probe(n, forms, target, dictionary=None, *, max_phase_evals=None):
    """Verify vanishing relations or a target indicator using unnormalized biases."""
    forms = tuple(forms)
    if n < 0 or not 0 <= target < 1 << len(forms):
        raise ValueError("invalid dimension or target")
    if max_phase_evals is not None and max_phase_evals < 0:
        raise ValueError("negative phase budget")
    normalized = [normalize(n, f) for f in forms]
    chars = tuple(dict.fromkeys(dictionary if dictionary is not None else
                                (0, *(1 << j for j in range(len(forms))))))
    if any(not isinstance(s, int) or not 0 <= s < 1 << len(forms) for s in chars):
        raise ValueError("invalid character")
    differences = {s ^ t for s in chars for t in chars} - {0}
    if max_phase_evals is not None and len(differences) > max_phase_evals:
        return GramResult("UNKNOWN", "budget", 0, chars)
    phases = {}
    used = 0

    def bias(mask, fixed, values, cache):
        nonlocal used
        if mask == 0:
            return 1 << (n - fixed.bit_count())
        if mask in cache:
            return cache[mask]
        if max_phase_evals is not None and used >= max_phase_evals:
            raise _BudgetExhausted
        if mask not in phases:
            phase = ZERO
            for j in bits(mask):
                phase = add(phase, normalized[j])
            phases[mask] = phase
        used += 1
        cache[mask] = gauss(n, phases[mask], fixed, values)
        return cache[mask]

    biases = {0: 1 << n}
    for mask in sorted(differences):
        bias(mask, 0, 0, biases)
    gram = [[biases[s ^ t] for t in chars] for s in chars]
    signs = [(-1 if parity(s & target) else 1) for s in chars]
    z, obstruction = _solve(gram, signs)
    if obstruction is not None:
        return GramResult("UNSAT", "annihilator", used, chars, obstruction, 0)
    energy = sum((v * x for v, x in zip(signs, z)), Fraction(0))
    bound = min(1 << n, (1 / energy).__floor__()) if energy else 1 << n
    if bound == 0:
        return GramResult("UNSAT", "integer bound", used, chars, count_upper=0, energy=energy)
    if not energy:
        return GramResult("UNKNOWN", "bound", used, chars, count_upper=bound, energy=energy)

    # Work with the unnormalized interpolant z·v, whose target value is E.
    # Its squared norm on the full input space is exactly E.
    weights = defaultdict(Fraction)
    for s, a in zip(chars, z):
        if not a:
            continue
        for t, b in zip(chars, z):
            if b:
                weights[s ^ t] += a * b
    weights = {u: a for u, a in weights.items() if a}

    def moment(shift, fixed, values, cache):
        return sum(a * bias(mask ^ shift, fixed, values, cache)
                   for mask, a in weights.items())

    try:
        for j in range(len(forms)):
            shifted = moment(1 << j, 0, 0, biases)
            if target & (1 << j):
                shifted = -shifted
            if shifted != energy:
                return GramResult("UNKNOWN", "bound", used, chars,
                                  count_upper=bound, energy=energy)
        exact = 1 / energy
        if exact.denominator != 1:
            raise ArithmeticError("nonintegral indicator count")
        fixed = witness = 0
        for j in range(n):
            fixed |= 1 << j
            if moment(0, fixed, witness, {}) == 0:
                witness |= 1 << j
        if evaluate(forms, witness) != target:
            raise ArithmeticError("target witness verification failed")
        return GramResult("SAT", "indicator", used, chars, count_upper=int(exact),
                          energy=energy, count=int(exact), witness=witness)
    except _BudgetExhausted:
        return GramResult("UNKNOWN", "budget", used, chars, count_upper=bound, energy=energy)
