"""Bounded original-secret enumeration for dynamic flat selection, h <= 8."""
from flat_selected_online import FlatLearner, SelectedQuery
from quadratic_polar_online import Quadratic


def pair(i, j):
    return 1 << (j * (j - 1) // 2 + i)


def value(query, seed):
    flags = tuple(inside(flat, seed) for flat in query.flats)
    row = query.specialize(flags)
    ones = [i for i in range(seed.bit_length()) if seed >> i & 1]
    result = row.constant ^ ((row.linear & seed).bit_count() % 2)
    for j in ones:
        for i in ones:
            if i < j and row.pairs & pair(i, j):
                result ^= 1
    return result


def inside(flat, seed):
    return all((seed & mask).bit_count() % 2 == bit for mask, bit in flat)


def hull(points):
    origin = min(points)
    span = {0}
    for point in points:
        direction = point ^ origin
        span |= {old ^ direction for old in span}
    return {origin ^ vector for vector in span}


def fixed(row):
    return SelectedQuery((), lambda flags: row)


ZERO = Quadratic(0, 0, 0)
ONE = Quadratic(1, 0, 0)


class Audit:
    def __init__(self, h, seed, r=0):
        self.model = FlatLearner(h, 0, r)
        self.universe = set(range(1 << h))
        self.feasible = self.universe.copy()
        self.history = ()
        self.seed = seed
        self.h = h

    def audit(self):
        model = self.model
        assert model.history == self.history
        flats = tuple(flat for query, _ in self.history for flat in query.flats)
        assert model.flats == flats
        groups = {}
        for seed in self.feasible:
            key = tuple(inside(flat, seed) for flat in flats)
            groups.setdefault(key, set()).add(seed)
        actual = {key: {s for s in self.universe if inside(eqs, s)}
                  for key, eqs in model.hulls.items()}
        assert actual == {key: hull(points) for key, points in groups.items()}
        return actual

    def step(self, query, counts):
        before = self.audit()
        ones = {s for s in self.feasible if value(query, s)}
        zeros = self.feasible - ones
        assert counts == (len(zeros), len(ones)) == self.model.histogram(query)
        guess = int(len(ones) > len(zeros))
        assert self.model.predict(query) == guess
        assert self.audit() == before
        label = value(query, self.seed)
        mistake = label != guess
        assert self.model.observe(query, label) == mistake
        if mistake:
            old = len(self.feasible)
            self.history += ((query, label),)
            self.feasible = ones if label else zeros
            assert 2 * len(self.feasible) <= old
        assert self.seed in self.feasible and len(self.history) <= self.h
        after = self.audit()
        if not mistake:
            assert after == before
        return after


def selectors():
    x0 = ((1, 0),)
    learner = Audit(1, 0)
    # Using each subflat's own readout in the subtraction gives (0,2).
    query = SelectedQuery((x0,), lambda f: ZERO if f[0] else ONE)
    learner.step(query, (1, 1))
    learner.step(SelectedQuery((x0,), lambda f: ONE if f[0] else ZERO), (1, 1))

    learner = Audit(3, 0)
    flats = (x0, ((2, 0),), ((2, 1),))
    after = learner.step(SelectedQuery(flats, lambda f: ONE if all(f[:2]) else ZERO), (6, 2))
    assert set(after) == {(True, True, False)}
    assert not any(tuple(inside(flat, s) for flat in flats) == (True, False, False)
                   for s in learner.universe)
    assert tuple(inside(flat, 3) for flat in flats) == (False, False, True)

    origin = (((1, 0), (2, 0), (4, 0)),)
    learner = Audit(3, 3)
    after = learner.step(SelectedQuery(origin, lambda f: ZERO if f[0] else Quadratic(1, 7, 0)), (5, 3))
    assert after == {(False,): {0, 3, 5, 6}} and learner.feasible == {3, 5, 6}
    learner.step(SelectedQuery(origin, lambda f: ONE if f[0] else ZERO), (3, 0))


def branches():
    learner = Audit(4, 11)
    x0 = (((1, 0),),)
    query = SelectedQuery(x0, lambda f: Quadratic(0, 0 if f[0] else 2, pair(1, 2)))
    assert learner.step(query, (12, 4)) == {(True,): {6, 14}, (False,): {3, 11}}
    query = SelectedQuery((((8, 0),),), lambda f: ZERO if f[0] else ONE)
    assert learner.step(query, (2, 2)) == {(True, False): {14}, (False, False): {11}}
    learner.step(SelectedQuery(x0, lambda f: ZERO if f[0] else ONE), (1, 1))


def shrinking():
    learner = Audit(6, 63)
    for i, expected in enumerate(((48, 16), (12, 4), (3, 1))):
        learner.step(fixed(Quadratic(0, 0, pair(2*i, 2*i+1))), expected)
        if i == 0:
            fresh = pair(0, 2) | pair(1, 3) | pair(4, 5)
            learner.step(fixed(Quadratic(1, 0, fresh)), (8, 8))
    assert learner.feasible == {63}

    learner = Audit(8, 243, r=1)
    base = pair(0, 1) | pair(2, 3)
    for extra, counts in ((0, (160, 96)), (pair(4, 5), (24, 72)), (pair(6, 7), (6, 18))):
        learner.step(fixed(Quadratic(0, 0, base | extra)), counts)
    assert len(learner.history) == 3


if __name__ == '__main__':
    selectors()
    branches()
    shrinking()
    print('Original-secret histogram, update, and feasible-hull checks passed.')
