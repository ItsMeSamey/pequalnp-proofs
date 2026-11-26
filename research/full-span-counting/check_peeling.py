#!/usr/bin/env python3
"""Recover exception-pattern masses by maximal positive superset moments."""
from fractions import Fraction
from itertools import combinations, product
from random import Random
from check_pattern import ONE, add, times, value
from check_robust import solve


def learn(m, features, moment):
    deleted = {}
    rounds = 0
    q = {1 << i: 1 for i in range(m)}
    def total(poly):
        return sum(c * moment(mask) for mask, c in poly.items())
    while True:
        bad = {}
        while True:
            coeff = solve([[value(f,v) for f in features] for v in bad], len(features))
            if coeff is None:
                assert len(bad) <= len(features)+1 and deleted.keys().isdisjoint(bad)
                deleted.update(bad)
                rounds += 1
                break
            f = add(*zip(coeff, features))
            err = add((1,ONE),(-1,f))
            energy = times(q, times(err,err))
            def upward(mask):
                return (sum(c*moment(mask | j) for j,c in energy.items()) -
                        sum(h*value(energy,v) for v,h in deleted.items() if v & mask == mask))
            mass = upward(0)
            if not mass:
                return total(ONE)-total(f)-sum(h*value(err,v) for v,h in deleted.items()), rounds, deleted
            mask = 0
            for i in range(m):
                candidate = mask | (1 << i)
                probe = upward(candidate)
                if probe:
                    assert probe > 0
                    mask, mass = candidate, probe
            h = Fraction(mass) / value(energy,mask)
            assert h > 0 and h.denominator == 1 and mask not in bad and mask not in deleted
            bad[mask] = int(h)


def main():
    rng = Random(58921)
    rounds_sum = 0
    for case in range(60):
        m,n = 5,5
        cubes = [tuple(rng.choice((-1,-1,-1,0,1)) for _ in range(n)) for _ in range(m)]
        counts = {}
        for x in product(range(2),repeat=n):
            v = sum(1 << i for i,cube in enumerate(cubes)
                    if all(a == -1 or a == b for a,b in zip(cube,x)))
            counts[v] = counts.get(v,0) + rng.choice((0,1,2**227+case,10**75+3))
        def moment(mask):
            return sum(h for v,h in counts.items() if v & mask == mask)
        features = [{1 << j:1 for j in range(m) if rng.randrange(2)} for _ in range(2)]
        answer, rounds, deleted = learn(m,features,moment)
        assert answer == counts.get(0,0)
        assert all(counts[v] == h for v,h in deleted.items())
        eligible = {v for v,h in counts.items() if v and h}
        # Any consistent optimum has a row basis of size at most p.
        rows = [[value(f,v) for f in features] for v in eligible]
        opt = len(rows)
        for size in range(3):
            for basis in combinations(rows,size):
                c = solve(basis,2)
                if c is not None:
                    faults = sum(sum(a*b for a,b in zip(r,c)) != 1 for r in rows)
                    opt = min(opt, faults)
        assert rounds <= opt <= len(deleted) <= 3*rounds
        rounds_sum += rounds
    print(f"60 exact maximal-pattern peeling cases passed, {rounds_sum} conflict rounds, 227+ bit masses.")


if __name__ == "__main__":
    main()
