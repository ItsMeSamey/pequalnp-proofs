"""Finite checks of clique parity, homogeneous restrictions, and product controls."""
from itertools import combinations

def rank(rows):
    pivots = {}
    for row in rows:
        while row:
            j = row.bit_length() - 1
            if j not in pivots:
                pivots[j] = row
                break
            row ^= pivots[j]
    return len(pivots)

def restrict_head(monomials, hyperplane):
    # H=0 expresses the highest-index selected variable as the XOR of the others.
    pivot = 1 << (hyperplane.bit_length() - 1)
    result = set()
    for mon in monomials:
        if not mon & pivot:
            result.symmetric_difference_update((mon,))
            continue
        for j in range(pivot.bit_length()-1):
            bit = 1 << j
            if hyperplane & bit and not mon & bit:
                result.symmetric_difference_update(((mon ^ pivot) | bit,))
    return result

def contraction_rank(monomials, n):
    rows = []
    for j in range(n):
        index = 1 << j
        rows.append(sum(1 << (mon ^ index) for mon in monomials if mon & index))
    return rank(rows)

def clique_table(n, k):
    edges = list(combinations(range(n), 2))
    cliques = [sum(1 << edges.index(e) for e in combinations(vs, 2)) for vs in combinations(range(n), k)]
    return [any(g & clique == clique for clique in cliques) for g in range(1 << len(edges))]

if __name__ == "__main__":
    for n in (2, 4):
        for k in range(2, n+1):
            assert sum(clique_table(n, k)) % 2 == 1
    head = {lo | (hi << 4) for lo in (3, 12) for hi in (3, 12)}
    histogram = {}
    for h in range(1, 256):
        contracted = contraction_rank(restrict_head(head, h), 8)
        histogram[contracted] = histogram.get(contracted, 0) + 1
        assert contracted > 4
    local = [b for b in range(16) if ((b & 3) == 3) ^ ((b & 12) == 12)]
    assert len(local) == 6
    assert all(a ^ b ^ c ^ d for a, b, c, d in combinations(local, 4))
    print('labeled graph parities checked at N=2,4')
    print('all 255 binary hyperplanes, contraction-rank histogram', sorted(histogram.items()))
    print('six-point support has no affine 2-flat')
