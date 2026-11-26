"""Small exhaustive audits of shared-span and branch-decomposition contraction."""
from collections import Counter
import random


def span(masks):
    values = {0}
    for a in masks:
        values |= {a ^ b for b in values}
    return values


def basis(space):
    known = {0}
    generators = []
    for a in sorted(space):
        if a not in known:
            generators.append(a)
            known |= {a ^ b for b in known}
    return generators


def trace(x, masks):
    return tuple((x & a).bit_count() % 2 for a in masks)


def eval_factor(x, terms, p):
    return sum(c * (-1)**trace(x, [a])[0] for a, c in terms) % p


def table(terms, p, n, external):
    """Count distinct linear functionals, not their ambient representatives."""
    def contract(ids):
        inside = span(terms[i][0] for i in ids)
        outside = span([terms[i][0] for i in range(len(terms)) if i not in ids] + external)
        boundary = basis(inside & outside)
        if len(ids) <= 1:
            result = Counter()
            reps = {}
            for x in range(1 << n):
                reps[trace(x, basis(inside))] = x
            for x in reps.values():
                val = eval_factor(x, [terms[i] for i in ids], p)
                result[trace(x, boundary), val] += 1
            return inside, boundary, result
        mid = len(ids)//2
        left, lb, lt = contract(ids[:mid])
        right, rb, rt = contract(ids[mid:])
        signatures = {(trace(x, lb), trace(x, rb), trace(x, boundary))
                      for x in range(1 << n)}
        result = Counter()
        for lkey, rkey, key in signatures:
            for a in range(p):
                for b in range(p):
                    result[key, (a+b) % p] += lt[lkey, a] * rt[rkey, b]
        return inside, boundary, result

    _, root_boundary, totals = contract(list(range(len(terms))))
    return root_boundary, totals


def test(rng):
    n = rng.randrange(1, 7)
    factors = []
    for _ in range(rng.randrange(1, 8)):
        p = rng.choice((3, 5, 7))
        terms = [(rng.randrange(1 << n), rng.randrange(p))
                 for _ in range(rng.randrange(0, 9))]
        factors.append((terms, p))
    spaces = [span(a for a, _ in terms) for terms, _ in factors]
    shared = span(a for i, space in enumerate(spaces)
                  for a in space & span(a for j, s in enumerate(spaces) if j != i for a in s))
    shared_basis = basis(shared)
    representatives = {trace(x, shared_basis): x for x in range(1 << n)}
    tables = [table(terms, p, n, shared_basis) for terms, p in factors]
    answer = 0
    for x in representatives.values():
        count = 1
        for (_, p), space, (boundary, totals) in zip(factors, spaces, tables):
            key = trace(x, boundary)
            local = [totals[key, val] for val in range(p)]
            assert sum(local) == len(space)//len(space & shared)
            count *= sum(local[1:])
        answer += count
    full = span(a for space in spaces for a in space)
    answer *= (1 << n)//len(full)
    brute = sum(all(eval_factor(x, terms, p) for terms, p in factors)
                for x in range(1 << n))
    assert answer == brute, (factors, answer, brute)


if __name__ == '__main__':
    rng = random.Random(241023)
    for _ in range(65):
        test(rng)
    print('65 shared-span counts matched exhaustive search')
