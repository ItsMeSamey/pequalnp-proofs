"""Original-matrix witness completion and three-dimensional determinant-cube controls."""
from itertools import combinations
from collections import Counter
import networkx as nx
from high_connectivity_anchor_check import host, mv


def reduce_rows(rows):
    basis = {}
    for row in rows:
        while row:
            pivot = row.bit_length() - 1
            if pivot not in basis:
                basis[pivot] = row
                break
            row ^= basis[pivot]
    return basis


def kernel_vector(rows):
    basis = reduce_rows(rows)
    free = next((i for i in range(len(rows)) if i not in basis), None)
    if free is None:
        return 0
    x = 1 << free
    for pivot, row in sorted(basis.items()):
        x |= ((row & x).bit_count() % 2) << pivot
    return x


def toggle(rows, d):
    return [row ^ (d & (1 << i)) for i, row in enumerate(rows)]


def determinant(rows):
    return int(len(reduce_rows(rows)) == len(rows))


def complete(A, pins, x):
    assert all(not (row >> i & 1) for i, row in enumerate(A))
    assert pins & x == pins and not x & mv(A, x)
    d = mv(A, x) & ~x
    while True:
        M = toggle(A, d)
        assert mv(M, x) == d
        v = kernel_vector(M)
        if not v:
            break
        if not v & x:
            x ^= v
        bit = (v & x) & -(v & x)
        d ^= bit
        assert len(reduce_rows(toggle(A, d))) == len(reduce_rows(M)) + 1
        assert x & pins == pins
    # Cofactors independently reconstruct every diagonal entry of the inverse.
    inverse_diag = 0
    for i in range(len(A)):
        minor = [row & ~(1 << i) for j, row in enumerate(M) if j != i]
        inverse_diag |= int(len(reduce_rows(minor)) == len(minor)) << i
        if pins >> i & 1:
            assert not determinant(toggle(M, 1 << i))
    assert inverse_diag == x and not x & mv(A, x)
    return d, x


def cube(rows):
    return sum(determinant(toggle(rows, d)) << d for d in range(8))


def isolated(signature):
    return [a for a in range(8) if signature >> a & 1 and
            all(not (signature >> (a ^ bit) & 1) for bit in (1, 2, 4))]


def reduced_cubes():
    by_nullity = []
    for t in range(4):
        signatures = set()
        for border in range(1 << (3 * t)):
            cross = [(border >> (3*i)) & 7 for i in range(t)]
            if len(reduce_rows(cross)) != t:
                signatures.add(0)
                continue
            for edges in range(8):
                rows = [0] * 3 + cross[:]
                for j, (a, b) in enumerate(combinations(range(3), 2)):
                    if edges >> j & 1:
                        rows[a] |= 1 << b
                        rows[b] |= 1 << a
                for i, c in enumerate(cross, 3):
                    for j in range(3):
                        rows[j] |= ((c >> j) & 1) << i
                sig = cube(rows)
                for shift in range(8):
                    signatures.add(sum(((sig >> (j ^ shift)) & 1) << j for j in range(8)))
        by_nullity.append(signatures)
    return by_nullity


def minimum_degree(signatures):
    for degree in range(9):
        mons = [u for u in range(256) if u.bit_count() <= degree]
        rows = [sum(int(s & u == u) << j for j, u in enumerate(mons)) for s in signatures]
        augmented = [2 * row + bool(isolated(s)) for s, row in zip(signatures, rows)]
        if len(reduce_rows(rows)) == len(reduce_rows(augmented)):
            return degree


def cycle_pivots():
    # Three terminals in cyclic order, two separated by even free paths.
    for a, b in ((2, 2), (2, 4), (4, 6)):
        n = a + b + 3
        pins = (0, a + 1, n - 1)
        G = nx.cycle_graph(n)
        A = [sum(1 << j for j in G[i]) for i in range(n)]
        remaining = set(G)
        work = A[:]
        for path in (range(1, a + 1), range(a + 2, n - 1)):
            for i in path[::2]:
                j = i + 1
                assert work[i] >> j & 1 and not work[i] >> i & 1 and not work[j] >> j & 1
                remaining -= {i, j}
                for v in remaining:
                    update = 0
                    if work[v] >> i & 1:
                        update ^= work[j]
                    if work[v] >> j & 1:
                        update ^= work[i]
                    work[v] ^= update & ~((1 << i) | (1 << j))
        reduced = [sum(((work[v] >> w) & 1) << k for k, w in enumerate(pins)) for v in pins]
        assert reduced == [6, 5, 3]
        for d in range(8):
            lift = sum(((d >> k) & 1) << v for k, v in enumerate(pins))
            assert determinant(toggle(A, lift)) == determinant(toggle(reduced, d))


def main():
    families = reduced_cubes()
    signatures = sorted(set.union(*families))
    histogram = Counter(len(isolated(s)) for s in signatures)
    degree = minimum_degree(signatures)
    print("per-nullity signatures", list(map(len, families)), "union", len(signatures),
          "isolates", sorted(histogram.items()), "minimum target degree", degree)
    print("even nonzero isolate count example", next(hex(s) for s in signatures
          if isolated(s) and len(isolated(s)) % 2 == 0))
    assert degree == 4 and len(signatures) == 136
    import sys
    if "--table" in sys.argv:
        print("signature,nullities,isolated_count,target")
        for sig in signatures:
            levels = "/".join(str(t) for t, family in enumerate(families) if sig in family)
            print(f"{sig:02x},{levels},{len(isolated(sig))},{int(bool(isolated(sig)))}")
    cycle_pivots()
    cases = 0
    for G in nx.graph_atlas_g():
        n = len(G)
        if not 3 <= n <= 5:
            continue
        A = [sum(1 << j for j in G[i]) for i in range(n)]
        for p in combinations(range(n), 3):
            pins = sum(1 << i for i in p)
            witnesses = [x for x in range(1 << n) if pins & x == pins and not x & mv(A, x)]
            have = False
            for d in range(1 << n):
                if d & pins:
                    continue
                sig = sum(determinant(toggle(A, d ^ sum(((s >> j) & 1) << i
                          for j, i in enumerate(p)))) << s for s in range(8))
                assert sig in signatures
                have |= bool(isolated(sig))
            assert have == bool(witnesses)
            for x in witnesses:
                complete(A, pins, x)
            cases += 1
    for t in range(1, 4):
        _, A, pins, m = host(t, True)
        mask = sum(1 << i for i in pins)
        complete(A, mask, mask | (1 << (pins[-1] + 1)))
        _, A, pins, m = host(t, False)
        left = (1 << m) - 1
        right = left << m
        p, q, r = pins
        assert A[q] == left | (1 << r) and A[r] == right | (1 << q)
        assert all((row & right) == right and (row & mask).bit_count() == 2 for row in A[:m])
        # q,r force odd selected counts on both shores. Left shore sum of
        # selected degrees is their product mod 2, by internal handshake.
    print("atlas pin sets", cases, "anchor pairs", 3)


if __name__ == "__main__":
    main()
