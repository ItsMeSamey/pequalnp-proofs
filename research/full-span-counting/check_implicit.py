#!/usr/bin/env python3
"""Compare implicit degree-bounded Boolean features with explicit tiny matrices."""
from fractions import Fraction
from itertools import combinations
from random import Random
from check_pattern import ONE, add, times, value, coords
from check_robust import solve


def positive_basis(rows,m,d):
    basis = []
    for _ in range(d):
        before = len(basis)
        for seed in [0]+basis[:]:
            for j in range(m):
                mask = seed | (1 << j)
                if coords(basis, rows, [int(v & mask == mask) for v in rows]) is None:
                    basis.append(mask)
        if len(basis) == before:
            break
    return basis


def full(rows,monomials):
    return [[int(v & mask == mask) for mask in monomials] for v in rows]


def checked_fit(rows,m,d,monomials):
    basis = positive_basis(rows,m,d)
    for mask in monomials:
        assert coords(basis,rows,[int(v & mask == mask) for v in rows]) is not None
    coeff = solve(full(rows,basis),len(basis))
    assert (coeff is None) == (solve(full(rows,monomials),len(monomials)) is None)
    if coeff is None:
        return None
    return {mask:c for mask,c in zip(basis,coeff) if c}


def learn(m,d,monomials,oracle):
    deleted = {}
    rounds = 0
    longest = 0
    q = {1 << j:1 for j in range(m)}
    while True:
        bad = {}
        while True:
            f = checked_fit(list(bad),m,d,monomials)
            if f is None:
                deleted.update(bad)
                rounds += 1
                longest = max(longest,len(bad))
                break
            err = add((1,ONE),(-1,f))
            energy = times(q,times(err,err))
            def upward(mask):
                return (sum(c*oracle(mask | k) for k,c in energy.items())
                        -sum(h*value(energy,v) for v,h in deleted.items() if v & mask == mask))
            mass = upward(0)
            if not mass:
                answer = oracle(0)-sum(c*oracle(k) for k,c in f.items())
                answer -= sum(h*value(err,v) for v,h in deleted.items())
                return answer,rounds,deleted,longest
            mask = 0
            for i in range(m):
                candidate = mask | (1 << i)
                probe = upward(candidate)
                if probe > 0:
                    mask,mass = candidate,probe
            assert mask not in bad and mask not in deleted
            bad[mask] = Fraction(mass)/value(energy,mask)


def main():
    rng = Random(337023)
    rounds_sum = 0
    for case in range(90):
        m = 5
        d = case % 4
        mons = [i for i in range(1,1 << m) if i.bit_count() <= d]
        patterns = rng.sample(range(1,1 << m),rng.randrange(1,9))
        if case % 3 == 0:
            patterns = list(range(1,8))  # degree one has inconsistent rows
        counts = {v:rng.choice((1,3,2**107+7)) for v in [0]+patterns}
        def oracle(mask):
            return sum(h for v,h in counts.items() if v & mask == mask)
        answer,rounds,deleted,longest = learn(m,d,mons,oracle)
        assert answer == counts[0] and all(counts[v] == h for v,h in deleted.items())
        rows = full(patterns,mons)
        for opt in range(len(rows)+1):
            if any(solve([r for i,r in enumerate(rows) if i not in omit],len(mons)) is not None
                   for omit in combinations(range(len(rows)),opt)):
                break
        rank = len(positive_basis(patterns,m,d))
        assert longest <= rank+1 and rounds <= opt <= len(deleted) <= (rank+1)*rounds
        rounds_sum += rounds
    print(f"90 implicit degree 0–3 cases passed, {rounds_sum} rounds; explicit spans, masses, optima and rank bounds checked.")


if __name__ == "__main__":
    main()
