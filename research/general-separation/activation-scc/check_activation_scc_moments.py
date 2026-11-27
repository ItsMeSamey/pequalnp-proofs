from random import Random
from activation_scc_moments import basis, features, masks, rank


def check(rows, rhs, d):
    n = len(rows)
    all_words = set()
    for x in range(1 << n):
        applied = sum(((x & row).bit_count() % 2) << i for i, row in enumerate(rows))
        if not (applied ^ rhs) & x:
            all_words.add(x)
    physical = basis(iter(rows), rhs, d)
    assert set(physical) <= all_words
    monomials = list(masks(range(n), d))
    actual_rank = rank(features(x, monomials) for x in all_words)
    returned_rank = rank(features(x, monomials) for x in physical)
    assert returned_rank == actual_rank == len(physical)


if __name__ == '__main__':
    rng = Random(314159)
    count = 0
    for n in range(8):
        for trial in range(25):
            rows = [rng.randrange(1 << n) for _ in range(n)]
            if trial & 1:
                rows = [r & ~((1 << (i & ~1)) - 1) for i, r in enumerate(rows)]
            if trial % 5 == 0:
                rows = [(1 << n) - 1 for _ in rows]
            check(rows, rng.randrange(1 << n), trial % 4)
            count += 1
    print(count, 'full-word truth-table comparisons of moments and genuine witnesses')
