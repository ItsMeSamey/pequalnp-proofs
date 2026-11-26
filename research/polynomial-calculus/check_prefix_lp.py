"""Check exact dual certificates for selected full mask-LP objectives (SciPy)."""
from fractions import Fraction
from random import Random

from scipy.optimize import linprog

from check_prefix_circulations import classify


def check(n, heads, tails, objective):
    m = len(heads)
    current = [sum(1 << e for e, group in enumerate(tails) if v in group)
               for v in range(n)]
    rows = []
    for e, h in enumerate(heads):
        old = current[h]
        current[h] ^= 1 << e
        rows.append((old, current[h]))
    masks = sorted({mask for edge in rows for mask in edge})
    indices = {mask: m + i for i, mask in enumerate(masks)}
    width = m + len(masks)
    # Each constraint is stored as lhs <= rhs; even bounds stay explicit.
    matrix, rhs = [], []
    def add(terms, bound, equality=False):
        row = [0] * width
        for i, c in terms:
            row[i] += c
        matrix.append(row)
        rhs.append(bound)
        if equality:
            matrix.append([-c for c in row])
            rhs.append(-bound)
    for i in range(width):
        add([(i, -1)], 0)
        add([(i, 1)], 1)
    for e, (old, new) in enumerate(rows):
        add([(indices[new], 1), (indices[old], -1), (e, 1)], 0, True)
    for mask, i in indices.items():
        add([(i, 1)] + [(e, -1) for e in range(m) if mask >> e & 1], 0,
            mask.bit_count() == 1)
    costs = objective + [0] * len(masks)
    result = linprog(costs, A_ub=matrix, b_ub=rhs, bounds=(None, None), method='highs')
    assert result.success
    dual = [Fraction(float(x)).limit_denominator(10000) for x in result.ineqlin.marginals]
    assert all(x <= 0 for x in dual)
    assert all(sum(x * row[i] for x, row in zip(dual, matrix)) == cost
               for i, cost in enumerate(costs))
    lower = sum(x * b for x, b in zip(dual, rhs))
    models = [x for x in range(1 << m)
              if all(not x >> e & 1 or (x & old).bit_count() % 2
                     for e, (old, _) in enumerate(rows))]
    best = min(sum(c for e, c in enumerate(objective) if x >> e & 1) for x in models)
    assert lower == best


def main():
    rng = Random(731)
    count = 0
    while count < 96:
        n = rng.randrange(2, 5)
        heads = [rng.randrange(n) for _ in range(rng.randrange(3, 8))]
        tails = [tuple(rng.sample(range(n), rng.choice([0, 1, 1, 1, 2])))
                 for _ in heads]
        if classify(n, heads, tails) is None:
            continue
        check(n, heads, tails, [rng.randint(-9, 9) for _ in heads])
        count += 1
    print(f'{count} full mask-LP optimum values verified by exact rational dual certificates.')


if __name__ == '__main__':
    main()
