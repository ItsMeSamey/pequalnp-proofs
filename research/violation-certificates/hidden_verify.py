"""Exhaust both sides of every 2+2 partition via exact truth tables."""
from itertools import combinations
from functools import cache
from verify import solve

N = 4
POINTS = range(1 << N)
FULL = (1 << len(POINTS)) - 1
UNIVERSE = ((1,), (-1,), (2,), (1,2), (1,-2), (-1,2), (-1,-2),
            (1,3), (-2,3), (3,4), (-3,4), (1,2,4))


def support(clause):
    return sum(1 << (abs(v)-1) for v in clause)


def violates(clause, x):
    return all(bool(x & (1 << (abs(v)-1))) != (v > 0) for v in clause)


@cache
def truth(formula):
    return sum(1 << x for x in POINTS if not any(violates(c,x) for c in formula))


@cache
def fit(formula, target):
    return solve([[violates(c,x) for c in formula] + [(target >> x) & 1] for x in POINTS],
                 len(formula))


def components(formula):
    parts = [1 << i for i in range(N)]
    for clause in formula:
        hit = [p for p in parts if p & support(clause)]
        parts = [p for p in parts if p not in hit] + [sum(hit)]
    return parts


def factor_count(formula, pins, values):
    result = 1
    for p in components(formula):
        local = tuple(c for c in formula if support(c) & p)
        result *= sum(1 for x in POINTS if not x & ~p and not (x ^ values) & p & pins
                      and truth(local) & (1 << x))
    return result


def run():
    counters = [0]*4
    for k in range(5):
        for formula in combinations(UNIVERSE,k):
            for side in (3,5,9):
                counters[0] += 1
                cross = tuple(c for c in formula if support(c) & side and support(c) & ~side)
                g = truth(cross)
                if fit(cross,FULL ^ g) is None:
                    continue
                counters[1] += 1
                d = tuple(c for c in formula if not g & ~truth((c,)))
                counters[2] += len(d)>len(cross)
                residual = tuple(c for c in formula if c not in d)
                weights = fit(d,FULL ^ g)
                assert weights is not None
                assert truth(formula) == g & truth(residual)
                parts = components(residual)
                assert any(sum(group).bit_count() == 2 for j in range(5)
                           for group in combinations(parts,j))
                essential = sum(1 << i for i in range(N) if any(
                    (g >> x ^ g >> (x ^ (1 << i))) & 1 for x in POINTS))
                counters[3] += essential.bit_count() < N and bool(cross)
                expected = truth(formula).bit_count()
                assert expected == sum(factor_count(residual,essential,x) for x in POINTS
                                       if not x & ~essential and (g >> x) & 1)
                weighted = factor_count(residual,0,0)
                for clause, w in zip(d, weights):
                    values = sum(1 << (-v-1) for v in clause if v < 0)
                    weighted -= w * factor_count(residual,support(clause),values)
                assert weighted == expected
    print('examined, fit, enlarged D, nonempty cross with inessential variable:', *counters)


if __name__ == '__main__':
    run()
