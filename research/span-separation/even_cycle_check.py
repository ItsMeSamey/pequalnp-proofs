"""Random small signed graphs, comparing the sparse-color algorithm with subset search."""
from itertools import combinations
from random import Random

def basis(values):
    pivots = {}
    for x in values:
        while x and x.bit_length() in pivots:
            x ^= pivots[x.bit_length()]
        if x:
            pivots[x.bit_length()] = x
    return list(pivots.values())

def contains(columns, x):
    return len(basis(columns + [x])) == len(basis(columns))

def brute(columns, K, w, u):
    for size in range(len(columns) + 1):
        for chosen in combinations(columns, size):
            X = list(chosen)
            if contains(X, u) and not contains(X + K, w):
                return True
    return False

def sparse_color(n, columns, K, w, u):
    k = len(basis(K))
    for color in (0, (1 << n)-1):
        for t in range(min(n, k)+1):
            for flips in combinations(range(n), t):
                f = color ^ sum(1 << i for i in flips)
                odd = lambda x: (x & f).bit_count() % 2
                if odd(w) and not any(odd(x) for x in K):
                    if contains([x for x in columns if not odd(x)], u):
                        return True
    return False

rng = Random(20261126)
for _ in range(1500):
    n = rng.randrange(1, 7)
    u = 1 << n
    edges = [(1 << rng.randrange(n)) ^ (1 << rng.randrange(n)) ^ (u*rng.randrange(2))
             for _ in range(rng.randrange(9))]
    K = [u] + [rng.randrange(2*u) for _ in range(rng.randrange(5))]
    w = rng.randrange(2*u)
    assert sparse_color(n, edges, K, w, u) == brute(edges, K, w, u)
print('1500 signed-graph instances matched all-subset search')
