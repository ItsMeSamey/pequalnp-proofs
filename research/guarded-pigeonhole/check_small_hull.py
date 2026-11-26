"""Check short-witness span versus ordinary PC2 exports on small guard systems."""
from itertools import combinations
from random import Random


def insert(basis, v):
    while v:
        i = v.bit_length() - 1
        if i not in basis:
            basis[i] = v
            return True
        v ^= basis[i]
    return False


def feasible(x, rows, b):
    return all(not (x >> i & 1) or (x & row).bit_count() % 2 == (b >> i & 1)
               for i, row in enumerate(rows))


def pc2(rows, b):
    n = len(rows)
    pair = {ij: n + k for k, ij in enumerate(combinations(range(n), 2))}
    def product(i, j):
        return 1 << (i if i == j else pair[min(i, j), max(i, j)])
    basis = {}
    for i, row in enumerate(rows):
        p = (b & (1 << i))
        for j in range(n):
            if row >> j & 1:
                p ^= product(i, j)
        insert(basis, p)
    while True:
        old = len(basis)
        linear = [p for i, p in basis.items() if i < n]
        for p in linear:
            for i in range(n):
                q = 0
                for j in range(n):
                    if p >> j & 1:
                        q ^= product(i, j)
                insert(basis, q)
        if len(basis) == old:
            return linear


def recognize(rows, b, limit):
    """Return (complete, independent actual models, PC2 linear equations)."""
    n = len(rows)
    basis = {}
    generators = []
    neighbors = [row & ~(1 << i) for i, row in enumerate(rows)]
    for i, row in enumerate(rows):
        for j in range(n):
            if (row >> j) & 1 and i != j:
                neighbors[j] |= 1 << i
    # Memoize endpoint and visited set. Every connected set has a traversal
    # staying inside itself; no length bound is needed after deduplication.
    stack = [(i, 1 << i) for i in range(n)] if limit else []
    seen_states = set(stack)
    tested = set()
    while stack:
        end, support = stack.pop()
        if support not in tested:
            tested.add(support)
            if feasible(support, rows, b) and insert(basis, support):
                generators.append(support)
        nxt = neighbors[end]
        while nxt:
            bit = nxt & -nxt
            nxt ^= bit
            new = (bit.bit_length() - 1, support | bit)
            if new[1].bit_count() <= limit and new not in seen_states:
                seen_states.add(new)
                stack.append(new)
    equations = pc2(rows, b)
    return len(generators) + len(equations) == n, generators, equations


def check(rows, b):
    n = len(rows)
    models = [x for x in range(1 << n) if feasible(x, rows, b)]
    lower, upper = {}, {}
    for x in models:
        insert(upper, x)
        if x.bit_count() <= 3:
            insert(lower, x)
    complete, generators, equations = recognize(rows, b, 3)
    assert len(generators) == len(lower)
    assert all(feasible(x, rows, b) and x.bit_count() <= 3 for x in generators)
    assert all((e & x).bit_count() % 2 == 0 for e in equations for x in models)
    assert len(lower) <= len(upper) <= n - len(equations)
    if complete:
        for ell in range(1 << n):
            witnesses = [x for x in models if (x & ell).bit_count() % 2]
            assert not witnesses or any(x.bit_count() <= 3 for x in witnesses)
        return 1
    return 0


def main():
    count = accepted = 0
    for n in (1, 2, 3):
        arcs = [(i, j) for i in range(n) for j in range(n) if i != j]
        for mask in range(1 << len(arcs)):
            rows = [0] * n
            for k, (i, j) in enumerate(arcs):
                if mask >> k & 1:
                    rows[i] |= 1 << j
            for b in range(1 << n):
                accepted += check(rows, b)
                count += 1
    rng = Random(217)
    for n in range(4, 9):
        for _ in range(60):
            rows = [rng.randrange(1 << n) & ~(1 << i) for i in range(n)]
            accepted += check(rows, rng.randrange(1 << n))
            count += 1
    for n in range(6, 31):
        rows = [(1 << ((i-1) % n)) | (1 << ((i+1) % n)) for i in range(n)]
        for i, j in ((0, 2), (2, 4), (4, 0)):
            rows[i] |= 1 << j
        b = (1 << n) - 1
        assert not pc2(rows, b)
        assert feasible(21, rows, b)
        assert all(feasible((1 << i) | (1 << ((i+1) % n)), rows, b) for i in range(n))
    for t in range(2, 12):
        for k in (3, 4, 5):
            n = k * t
            rows = [1 << ((i + 1) % n) for i in range(n)]
            rows[t-1] |= 1 << (2*t-1)
            b = sum(1 << i for i in range(n) if i % t != t-1)
            assert not pc2(rows, b)
            for first in range(0, n, t):
                end = first + t
                for start in range(first, end):
                    suffix = ((1 << end) - 1) ^ ((1 << start) - 1)
                    assert feasible(suffix, rows, b)
            if n <= 12:
                assert min(x.bit_count() for x in range(1, 1 << n, 2)
                           if feasible(x, rows, b)) == t
    print(f'{count} exhaustive or seeded systems, {accepted} hull equalities, 25 cycle-triangle sizes, 30 hierarchy examples.')


if __name__ == '__main__':
    main()
