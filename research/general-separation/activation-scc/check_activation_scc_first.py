from itertools import product
from random import Random
from activation_scc_first import basis, dot
from activation_scc_moments import bits, rank


def check(rows, b):
    n = len(rows)
    actual = {x for x in range(1 << n) if all(dot(rows[i], x) == (b >> i & 1) for i in bits(x))}
    witnesses = basis(iter(rows), b)
    assert set(witnesses) <= actual
    assert len(witnesses) == rank(witnesses) == rank(actual)


if __name__ == '__main__':
    tested = 0
    for n in range(4):
        for rows in product(range(1 << n), repeat=n):
            for b in range(1 << n):
                check(rows, b)
                tested += 1
    gen = Random(1984)
    for n in range(4, 10):
        for trial in range(32):
            rows = [gen.randrange(1 << n) for i in range(n)]
            if trial & 1:
                rows = [r & ~((1 << (i & ~1)) - 1) for i, r in enumerate(rows)]
            check(rows, gen.randrange(1 << n))
            tested += 1
    print(tested, 'direct feasible-word span comparisons')
