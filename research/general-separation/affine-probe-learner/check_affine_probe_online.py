"""Bounded original-secret audit for the arbitrary-readout, residual-rank learner.

The weighted bound is tested here. The exact h bound is for a separate quadratic
halving algorithm; this checker does not claim it for the learner under test.
"""
from collections import Counter
from random import Random
from affine_probe_online import AffineProbeLearner


def span(rows):
    values = {0}
    for row in rows:
        values |= {v ^ row for v in tuple(values)}
    return frozenset(values)


def measurement(rows, offset, seed):
    return offset ^ sum(((row & seed).bit_count() % 2) << j for j, row in enumerate(rows))


def snapshot(learner, h, k):
    cells = Counter()
    numerator = 0
    for basis, origin, directions in learner.committed_cells():
        dual = span(basis)
        points = frozenset(origin ^ x for x in span(directions))
        assert all(0 <= v < 1 << h for v in (*basis, origin, *directions))
        assert len(dual) == 1 << len(basis) and len(points) == 1 << len(directions)
        assert len(basis) <= k
        assert all(len({(v & s).bit_count() % 2 for s in points}) == 1 for v in basis)
        cells[dual, points] += 1
        numerator += len(points) * 7 ** (k - len(basis))
    assert sum(cells.values()) == learner.expert_count
    assert learner.mass_denominator == 7 ** k
    assert learner.mass_numerator == numerator <= (1 << h) * 7 ** k
    return cells, numerator


class Audit:
    def __init__(self, h, k, secret, target):
        self.h, self.k, self.secret = h, k, secret
        self.target = span(target)
        self.learner = AffineProbeLearner(h, k)
        cells, mass = snapshot(self.learner, h, k)
        assert cells == Counter({(frozenset({0}), frozenset(range(1 << h))): 1})
        assert mass == (1 << h) * 7 ** k
        self.paths = list(cells)
        self.transcript = []

    def oracle(self, cells, rows, offset, table, truth):
        """Explicit sets and direct per-secret lookup; no linear-system implementation."""
        votes = [0, 0]
        after = Counter()
        def visit(dual, points, n):
            independent = []
            covered = dual
            for row in rows:
                if row not in covered:
                    independent.append(row)
                    covered = covered | {u ^ row for u in covered}
                    if len(independent) == 3:
                        break
            if len(independent) == 3:
                if len(dual) == 1 << self.k:
                    return
                for form in span(independent) - {0}:
                    extended = dual | {u ^ form for u in dual}
                    one = frozenset(s for s in points if (s & form).bit_count() % 2)
                    for group in (one, points - one):
                        if group:
                            visit(extended, group, n)
                return
            correct = frozenset(s for s in points if table[measurement(rows, offset, s)] == truth)
            ones = len(correct) if truth else len(points) - len(correct)
            own = int(2 * ones > len(points))
            votes[own] += n * len(points) * 7 ** (self.k - (len(dual).bit_length()-1))
            retained = points if own == truth else correct
            if retained:
                after[dual, retained] += n
        for (dual, points), multiplicity in cells.items():
            visit(dual, points, multiplicity)
        return votes, after

    def run(self, rows, offset, table, observe=False):
        learner, k = self.learner, self.k
        rows = tuple(rows)
        truth = table[measurement(rows, offset, self.secret)]
        before, old_mass = snapshot(learner, self.h, k)
        mistakes = learner.mistakes
        calls = []
        def callback(i):
            calls.append(i)
            return table[i]
        bit = learner.predict(rows, offset, callback if observe else table)
        assert bit in (0, 1)
        T = span(rows)
        votes, expected_after = self.oracle(before, rows, offset, table, truth)
        assert sum(votes) <= old_mass
        assert bit == int(votes[1] > votes[0])
        wrong = bit != truth
        assert learner.update(truth) == wrong
        after, new_mass = snapshot(learner, self.h, k)
        assert learner.mistakes == mistakes + int(wrong)
        if not wrong:
            assert after == before and new_mass == old_mass
        else:
            assert after == expected_after
            assert len({u^v for u in T for v in self.target}) <= 4*len(self.target)
            assert 4*new_mass <= 3*old_mass
            # Track a consistent chain across committed rounds, including both
            # actual secret containment and the promised dual subspace.
            self.paths = [(d, a) for d, a in after if d <= self.target and self.secret in a
                          and any(e <= d and a <= b for e, b in self.paths)]
            assert self.paths and new_mass >= 1
        m = learner.mistakes
        assert 4**m <= (1 << self.h) * 7**k * 3**m
        self.transcript.append((bit, truth))
        return bit, truth, calls, after, new_mass


def fixtures():
    zero = Audit(0, 0, 0, ())
    for offset in range(8):
        zero.run((0,0,0), offset, (0,0,1,1,0,1,0,0))

    h, k, secret = 6, 2, 39
    audit = Audit(h, k, secret, (1,2))
    full_rank = [1 << j for j in range(h)]
    # More than two residual measurements at budget exhaustion. Default zero
    # is correct; even an empty provisional expert set must roll back.
    b, y, calls, after, _ = audit.run(full_rank, 21, [0]*64, True)
    assert (b,y)==(0,0) and not calls and sum(after.values())==1
    # Two splits on the same query, first provisionally and then committed.
    rows = (1,2,4,8,3,0)
    offset = 53
    b, y, calls, after, _ = audit.run(rows, offset, [0]*64, True)
    assert (b,y)==(0,0) and calls and sum(after.values())==1
    # A singleton on a four-dimensional image has Boolean degree four.
    reachable = {measurement(rows, offset, s) for s in range(1 << h)}
    desired = measurement(rows, offset, secret)
    table = [int(j==desired) if j in reachable else (j^(j>>3)).bit_count()%2 for j in range(64)]
    b, y, calls, after, mass = audit.run(rows, offset, table, True)
    fibre = frozenset(s for s in range(1 << h) if measurement(rows, offset, s)==desired)
    assert (b,y)==(0,1) and set(calls) <= reachable
    assert all(len(d)==4 and a==fibre for d,a in after)
    assert mass==49*len(fibre)
    # High-rank correct noise now tests restoration of nontrivial committed cells.
    b, y, calls, _, _ = audit.run(full_rank, 31, [0]*64, True)
    assert (b,y)==(0,0) and not calls
    for r in [(16,), (32,), (16,32,48,0)]:
        audit.run(r, 1, [int(j.bit_count()%3==1) for j in range(1 << len(r))])
    return len(audit.transcript) + len(zero.transcript)


def adaptive():
    rounds = mistakes = 0
    for secret in range(16):
        audit = Audit(4, 1, secret, (3,))
        rng = Random(7104)
        for _ in range(24):
            last = audit.transcript[-1][1] if audit.transcript else 0
            a = rng.randrange(16)^last
            b = rng.randrange(16)
            rows = (3,a,b,a^b^3,0)
            table = tuple(rng.randrange(2) for _ in range(32))
            audit.run(rows, rng.randrange(32), table)
        rounds += len(audit.transcript)
        mistakes += audit.learner.mistakes
    return rounds, mistakes


if __name__ == "__main__":
    print("fixture rounds", fixtures())
    print("adaptive rounds and mistakes", adaptive())
