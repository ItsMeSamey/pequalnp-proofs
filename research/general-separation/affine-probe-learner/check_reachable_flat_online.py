"""Independent original-seed checks for sparse reachable signatures, h <= 6."""
from itertools import combinations

from reachable_flat_online import Quadratic, ReachableFlatLearner, SelectedQuery


ZERO = Quadratic(0, 0, 0)
ONE = Quadratic(1, 0, 0)


def inside(seed, equations):
    return all((seed & mask).bit_count() % 2 == rhs for mask, rhs in equations)


def flags(seed, flats):
    return tuple(inside(seed, flat) for flat in flats)


def evaluate(seed, query):
    row = query.specialize(flags(seed, query.flats))
    bit = row.constant ^ ((seed & row.linear).bit_count() % 2)
    active = [i for i in range(seed.bit_length()) if seed & (1 << i)]
    for i, j in combinations(active, 2):
        bit ^= (row.pairs >> (j * (j - 1) // 2 + i)) & 1
    return bit


def affine_closure(points):
    origin = min(points)
    result = {origin}
    for point in points:
        result |= {x ^ point ^ origin for x in result}
    return result


def fixed(row):
    return SelectedQuery((), lambda _: row)


class Audit:
    def __init__(self, h, target, signatures, cells=None):
        self.model = ReachableFlatLearner(h, 0, 2, signatures, max_cells=cells)
        self.all = set(range(1 << h))
        self.live = self.all.copy()
        self.history = ()
        self.target = target
        self.check_state()

    def check_state(self):
        assert self.model.history == self.history
        flats = tuple(f for q, _ in self.history for f in q.flats)
        assert self.model.flats == flats
        groups = {}
        for x in self.live:
            groups.setdefault(flags(x, flats), set()).add(x)
        reported = {key: {x for x in self.all if inside(x, eqs)}
                    for key, eqs in self.model.hulls.items()}
        assert reported == {key: affine_closure(xs) for key, xs in groups.items()}

    def step(self, q):
        ones = {x for x in self.live if evaluate(x, q)}
        totals = len(self.live) - len(ones), len(ones)
        assert self.model.histogram(q) == totals
        prediction = int(totals[1] > totals[0])
        assert self.model.predict(q) == prediction
        label = evaluate(self.target, q)
        changed = label != prediction
        assert self.model.observe(q, label) == changed
        if changed:
            self.live = ones if label else self.live - ones
            self.history += ((q, label),)
        self.check_state()
        return totals

    def clipped(self, q):
        assert self.model.histogram(q) is None
        assert self.model.predict(q) == 0
        try:
            self.model.observe(q, evaluate(self.target, q))
        except ValueError as exc:
            assert "budget" in str(exc)
        else:
            raise AssertionError("expected budget failure")
        self.check_state()


def missing_historical_mask():
    # Three accepted points 4,5,6 span the proper affine plane 4..7.
    # Frozen false-branch history also accepts 7, despite the actual old
    # membership being true there. Its contribution must be subtracted.
    singleton = ((1, 1), (2, 1), (4, 1))
    old = SelectedQuery((singleton,), lambda f: ZERO if f[0] else Quadratic(0, 4, 0))
    for hidden in (4, 5, 6):
        run = Audit(3, hidden, 2)
        assert run.step(old) == (5, 3)
        assert run.live == {4, 5, 6}
        assert run.step(fixed(Quadratic(0, 0, 1))) == (3, 0)
        run.step(fixed(Quadratic(0, 1, 0)))


def many_intersections():
    h = 6
    run = Audit(h, (1 << h) - 1, 1, 1)
    for j in range(h):
        run.step(fixed(Quadratic(0, 1 << j, 0)))
    flats = tuple(((1 << j, 1),) for j in range(h))
    # The coordinate hyperplanes have 2**h distinct formal intersections.
    # Compute those sets extensionally without any arrangement code.
    intersections = {frozenset(run.all)}
    for f in flats:
        subset = {x for x in run.all if inside(x, f)}
        intersections |= {s & subset for s in intersections}
    assert len(intersections) == 1 << h
    assert run.live == {(1 << h) - 1}
    assert run.step(SelectedQuery(flats, lambda bits: ONE if all(bits) else ZERO)) == (0, 1)


def empty_negative_and_caps():
    complementary = (((1, 0),), ((1, 1),))
    def selector(bits):
        assert sum(bits) == 1, "specialized an empty atom"
        return Quadratic(0, 2 if bits[0] else 1, 0)
    q = SelectedQuery(complementary, selector)
    Audit(2, 0, 2, 2).step(q)
    Audit(2, 0, 1, 2).clipped(q)
    Audit(2, 0, 2, 1).clipped(q)
    Audit(2, 0, 2, 0).clipped(fixed(ZERO))


if __name__ == "__main__":
    missing_historical_mask()
    many_intersections()
    empty_negative_and_caps()
    print("reachable signature oracle checks passed")
