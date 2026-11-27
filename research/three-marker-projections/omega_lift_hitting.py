"""Deterministic bounded-private-rank hitting for a two-bit lift and alternating Ω."""
from dataclasses import dataclass
from importlib.util import module_from_spec, spec_from_file_location
from itertools import combinations
from pathlib import Path

from component_nullity import bits, dependencies
from thick_tag_solver import basis, combine, reduce_vector

_spec = spec_from_file_location(
    "neutral_routing", Path(__file__).resolve().parents[1] / "span-separation/neutral_routing.py"
)
_field = module_from_spec(_spec)
_spec.loader.exec_module(_field)


@dataclass
class Witness:
    basis_ids: list
    x: list
    y: list
    predictions: list


def sample_predictions(coordinates, rank, p):
    """Hit every two-bit linear prescription on any subspace of dimension <= p."""
    minimum = max(2, 1 << p, (rank - 1) * ((1 << p) - 1) + 1)
    degree = (minimum - 1).bit_length()
    q = 1 << degree
    modulus = _field.irreducible(degree)
    for b in range(q):
        powers = [1]
        for _ in range(1, rank):
            powers.append(_field.mul(powers[-1], b, modulus))
        evaluations = [combine(powers, mask) for mask in coordinates]
        for a in range(q):
            low = [(a & value).bit_count() % 2 for value in evaluations]
            for c in range(q):
                yield [lo | (((c & value).bit_count() % 2) << 1)
                       for lo, value in zip(low, evaluations)]


def solve(private, tags, omega, p):
    """Return an actual full private basis, fundamental pair and induced tags.

    omega acts on original-index support bitmasks and must be alternating bilinear
    on the private kernel. A miss excludes witnesses whose joint support has
    private rank at most p. A hit may have greater support rank.
    """
    private, tags = list(private), list(tags)
    if (type(p) is not int or p < 0 or len(private) != len(tags)
            or any(type(v) is not int or v < 0 for v in private)
            or any(type(t) is not int or t not in range(4) for t in tags)):
        raise ValueError("invalid rank bound or physical columns")
    pivots, initial = basis(private)
    rank = len(initial)
    coordinates = [reduce_vector(v, pivots)[1] for v in private]
    for predictions in sample_predictions(coordinates, rank, p):
        active = [i for i, (v, t) in enumerate(zip(predictions, tags)) if v == t]
        local = dependencies([coordinates[i] for i in active])
        cycles = [sum(1 << active[j] for j in bits(mask)) for mask in local]
        for x, y in combinations(cycles, 2):
            if not omega(x, y):
                continue
            # Last set position is each fundamental circuit's distinct chord.
            chord_x, chord_y = x.bit_length() - 1, y.bit_length() - 1
            core = list(bits((x | y) ^ (1 << chord_x) ^ (1 << chord_y)))
            order = core + initial
            chart, chosen = basis([private[i] for i in order])
            ids = [order[j] for j in chosen]
            chart_tags = [tags[i] for i in ids]
            actual = [combine(chart_tags, reduce_vector(v, chart)[1]) for v in private]
            if any(actual[i] != tags[i] for i in bits(x | y)):
                raise AssertionError("completion changed a required tag")
            return Witness(ids, list(bits(x)), list(bits(y)), actual)
    return None


def check_small():
    """Directly enumerate joint supports and kernel words for small controls."""
    from random import Random
    rng = Random(417)
    for trial in range(64):
        n = rng.randrange(2, 7)
        private = [rng.randrange(4) << 31 for _ in range(n)]
        tags = [rng.randrange(4) if trial % 3 else 0 for _ in range(n)]
        p = trial % 3
        rows = [rng.randrange(1 << n) for _ in range(n)]

        def omega(x, y):
            xy = sum((rows[i] & y).bit_count() for i in bits(x))
            yx = sum((rows[j] & x).bit_count() for j in bits(y))
            return (xy + yx) % 2

        kernel = [m for m in range(1 << n) if not combine(private, m)]
        found, bounded = False, False
        for x, y in combinations(kernel, 2):
            if not omega(x, y):
                continue
            support = x | y
            if any(combine(tags, z) for z in kernel if z & ~support == 0):
                continue
            found = True
            if len(basis([private[i] for i in bits(support)])[1]) <= p:
                bounded = True
        answer = solve(private, tags, omega, p)
        if answer is None:
            assert not bounded
            continue
        assert found
        x, y = (sum(1 << i for i in indices) for indices in (answer.x, answer.y))
        assert x in kernel and y in kernel and omega(x, y)
        pivots, independent = basis([private[i] for i in answer.basis_ids])
        assert len(answer.basis_ids) == len(independent) == len(basis(private)[1])
        chords = [set(word) - set(answer.basis_ids) for word in (answer.x, answer.y)]
        assert all(len(s) == 1 for s in chords) and chords[0] != chords[1]
        chart_tags = [tags[i] for i in answer.basis_ids]
        assert answer.predictions == [combine(chart_tags, reduce_vector(v, pivots)[1])
                                      for v in private]
        assert all(answer.predictions[i] == tags[i] for i in bits(x | y))


if __name__ == "__main__":
    check_small()
    print("64 capped exhaustive support comparisons passed")
