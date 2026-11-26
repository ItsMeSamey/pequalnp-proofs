#!/usr/bin/env python3
"""Projected pattern learner. The learner sees positive-monomial moments and witness rows."""
from fractions import Fraction
from itertools import product
from random import Random
from check_robust import solve

ONE = {0: 1}


def add(*terms):
    result = {}
    for scale, poly in terms:
        for mask, c in poly.items():
            result[mask] = result.get(mask, 0) + scale*c
    return {m:v for m,v in result.items() if v}


def times(a,b):
    result = {}
    for i,x in a.items():
        for j,y in b.items():
            k = i | j
            result[k] = result.get(k, 0) + x*y
    return {m:v for m,v in result.items() if v}


def value(poly,v):
    return sum(c for m,c in poly.items() if m & v == m)


def coords(basis, points, target):
    rows = [[Fraction(mask & v == mask) for mask in basis]+[Fraction(y)]
            for v,y in zip(points,target)]
    for i in range(len(basis)):
        pivot = next(j for j in range(i,len(rows)) if rows[j][i])
        rows[i], rows[pivot] = rows[pivot], rows[i]
        div = rows[i][i]
        rows[i] = [x/div for x in rows[i]]
        for j, row in enumerate(rows):
            if i != j:
                scale = row[i]
                rows[j] = [a-scale*b for a,b in zip(row,rows[i])]
    if any(row[-1] for row in rows[len(basis):]):
        return None
    return {m:rows[i][-1] for i,m in enumerate(basis) if rows[i][-1]}


def border(points,m):
    if not points:
        return ONE, {}
    basis = [0]
    for mask in basis:  # new independent columns are also visited
        for i in range(m):
            k = mask | (1 << i)
            if coords(basis,points,[(k & v) == k for v in points]) is None:
                basis.append(k)
    assert len(basis) == len(points)
    W = {}
    for mask in basis:
        for i in range(m):
            k = mask | (1 << i)
            rep = coords(basis,points,[(k & v) == k for v in points])
            r = add((1,{k:1}),(-1,rep))
            W = add((1,W),(1,times(r,r)))
    h = coords(basis,points,[Fraction(1,v.bit_count()) for v in points])
    return W,h


def learn(m,n,feature,lookup,moment):
    p = len(feature)
    Q = {1 << i:1 for i in range(m)}
    deleted = []
    rounds = 0
    while True:
        W,h = border(deleted,m)
        assert {v for v in range(1 << m) if not value(W,v)} == set(deleted)
        weight = times(Q,W)
        bad = []
        while True:
            coeff = solve([[value(f,v) for f in feature] for v in bad],p)
            if coeff is None:
                assert len(bad) <= p+1 and set(bad).isdisjoint(deleted)
                deleted.extend(bad)
                rounds += 1
                break
            f = add(*zip(coeff,feature))
            err = add((1,ONE),(-1,f))
            energy = times(weight,times(err,err))
            def count(poly,prefix=()):
                return sum(c*moment(mask,prefix) for mask,c in poly.items())
            if not count(energy):
                answer = count(ONE)-count(f)-count(times(times(Q,err),h))
                return answer,rounds,deleted
            prefix = ()
            for _ in range(n):
                prefix += (0 if count(energy,prefix+(0,)) else 1,)
            v = lookup(prefix)
            assert v and v not in bad and v not in deleted
            bad.append(v)


def main():
    rng = Random(278007)
    total_rounds = 0
    for case in range(20):
        m,n = 4,4
        xs = list(product(range(2),repeat=n))
        cubes = [tuple(rng.choice((-1,-1,0,1)) for _ in range(n)) for _ in range(m)]
        patterns = {x:sum(1 << i for i,cube in enumerate(cubes)
                          if all(a == -1 or a == b for a,b in zip(cube,x))) for x in xs}
        weights = {x:rng.choice([0,1,5,2**201+37,10**64+case]) for x in xs}
        feature = [{1 << j:1 for j in range(m) if rng.randrange(2)} for _ in range(2)]
        def moment(mask,prefix):
            # Match the pins of each selected falsifying cube, and the prefix.
            return sum(weights[x] for x in xs if x[:len(prefix)] == prefix and
                       all(all(a == -1 or a == b for a,b in zip(cubes[i],x))
                           for i in range(m) if mask >> i & 1))
        answer, rounds, deleted = learn(m,n,feature,patterns.__getitem__,moment)
        assert answer == sum(weights[x] for x in xs if not patterns[x])
        from itertools import combinations
        eligible = {patterns[x] for x in xs if weights[x] and patterns[x]}
        for opt in range(len(eligible)+1):
            if any(solve([[value(f,v) for f in feature] for v in eligible-set(omit)],2)
                   is not None for omit in combinations(eligible,opt)):
                break
        assert rounds <= opt <= len(deleted) <= 3*rounds
        total_rounds += rounds
    print(f"20 exact pattern systems passed, {total_rounds} greedy rounds, 200+ bit multiplicities.")


if __name__ == "__main__":
    main()
