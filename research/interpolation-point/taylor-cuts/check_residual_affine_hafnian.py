"""Small exact comparisons for normalized affine products."""
from collections import Counter
from functools import cache
from itertools import combinations, product
from math import prod
from random import Random


def v2(x):
    return (abs(x) & -abs(x)).bit_length() - 1 if x else 10**6


def marked_hafnian(c, a, m):
    b = len(c)
    n = b + m

    @cache
    def solve(vertices):
        if not vertices:
            return Counter({0: 1})
        i, *rest = vertices
        answer = Counter()
        for j in rest:
            weight = degree = 0
            if i < b <= j < n:
                weight, degree = a[i][j-b], 1
            elif i < n and j == n+i:
                weight = c[i] if i < b else 1
            elif i >= n:
                weight = 1
            if weight:
                for k, value in solve(tuple(t for t in rest if t != j)).items():
                    answer[degree+k] += weight * value
        return answer

    result = 0
    for degree, value in solve(tuple(range(2*n))).items():
        odd = prod(range(1, 2*degree, 2))
        assert value % odd == 0
        result += value // odd
    return result


def check(c, a, m):
    b = len(c)
    bits = list(product(range(2), repeat=m))
    def row(i, x):
        return c[i] + sum(2*t*v for t,v in zip(x, a[i]))
    num = sum(prod(row(i,x) for i in range(b)) for x in bits)
    assert num % (1<<m) == 0
    exact = num // (1<<m)
    collision_terms = []
    free_matching = 0
    for choice in product(range(-1,m), repeat=b):
        used = [j for j in choice if j >= 0]
        excess = len(used)-len(set(used))
        weight = prod(c[i] if j < 0 else a[i][j] for i,j in enumerate(choice))
        collision_terms.append((excess, weight<<excess))
        if not excess:
            free_matching += weight
    assert marked_hafnian(c,a,m) == free_matching
    assert sum(v for _,v in collision_terms) == exact
    assert v2(exact) >= min(v2(v) for _,v in collision_terms)
    if any(not c[i] and not any(a[i]) for i in range(b)):
        assert not exact
        return
    d = [min([v2(c[i])]+[1+v2(v) for v in a[i]]) for i in range(b)]
    fibers = [[row(i,x)//(1<<d[i]) for i in range(b)] for x in bits]
    s = sum(prod(values) for values in fibers)
    assert (s << sum(d)) == num
    assert (s%2 == 1) == (sum(all(v%2 for v in values) for values in fibers) == 1)
    for h in range(1,5):
        mod = 1<<h
        assert sum(v for e,v in collision_terms if e<h)%mod == exact%mod
        total = 0
        for values in fibers:
            even = [v for v in values if v%2 == 0]
            odd = [v-1 for v in values if v%2 == 1]
            for k in range(min(len(odd)+1,h-len(even))):
                total += prod(even)*sum(prod(t) for t in combinations(odd,k))
        assert total % mod == s % mod


if __name__ == '__main__':
    rng = Random(237)
    for b,m in product(range(1,6),range(1,5)):
        for _ in range(12):
            check([rng.randrange(-4,5) for i in range(b)],
                  [[rng.randrange(-4,5) for j in range(m)] for i in range(b)], m)
    print('240 signed affine products verified through modulus 16')
