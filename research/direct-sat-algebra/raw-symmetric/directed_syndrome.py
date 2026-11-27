"""Syndromes of nonsingular principal sets of arbitrary binary matrices."""
from itertools import combinations
from symmetric_syndrome import invertible


def syndrome_bound(rows, labels, target):
    """Return safe radius, or None when target is outside the label span."""
    n = len(rows)
    if len(labels) != n or target < 0 or any(v < 0 for v in labels):
        raise ValueError("invalid syndrome data")
    if any(not 0 <= v < 1 << n for v in rows):
        raise ValueError("invalid matrix row")
    # Reduce the syndrome constraints jointly with their right sides.
    pivots = {}
    for a in range(max([target, *labels]).bit_length()):
        row = sum((x >> a & 1) << i for i, x in enumerate(labels))
        b = target >> a & 1
        while row:
            j = row.bit_length() - 1
            if j not in pivots:
                pivots[j] = row, b
                break
            h, c = pivots[j]
            row ^= h
            b ^= c
        else:
            if b:
                return None
    reach = [r | (1 << i) for i, r in enumerate(rows)]
    for k in range(n):
        for i in range(n):
            if reach[i] >> k & 1:
                reach[i] |= reach[k]
    blocks = []
    for i in range(n):
        block = tuple(j for j in range(n) if reach[i] >> j & reach[j] >> i & 1)
        if i != block[0] or len(block) < 3:
            continue
        if not any(((rows[u] >> v) ^ (rows[v] >> u)) & 1 for u, v in combinations(block, 2)):
            continue
        # A connected simple undirected cycle has only one long cycle support.
        cycle = all(sum((rows[u] >> v | rows[v] >> u) & 1 for v in block if v != u) == 2
                    for u in block)
        blocks.append((sum(1 << v for v in block), cycle))
    bound = 0
    for h, _ in pivots.values():
        cap = int(any(rows[i] >> i & h >> i & 1 for i in range(n)))
        if any(rows[i] >> j & rows[j] >> i & ((h >> i) ^ (h >> j)) & 1
               for i, j in combinations(range(n), 2)):
            cap = 2
        for mask, simple_cycle in blocks:
            part = mask & h
            if part and (not simple_cycle or part.bit_count() % 2):
                cap = max(cap, mask.bit_count())
        bound += cap
    return min(n, bound)


def principal_witness(rows, labels, target):
    """Return packed support, including 0 for the empty set, or None."""
    bound = syndrome_bound(rows, labels, target)
    if bound is None:
        return None
    for k in range(bound + 1):
        for subset in combinations(range(len(rows)), k):
            mask = label = 0
            for i in subset:
                mask |= 1 << i
                label ^= labels[i]
            if label == target and invertible([rows[i] & mask for i in subset]):
                return mask
    return None


if __name__ == "__main__":
    from random import Random
    rng = Random(728)
    for n in range(1, 9):
        for _ in range(12):
            rows = [rng.randrange(1 << n) for i in range(n)]
            labels = [rng.randrange(4) for i in range(n)]
            true = {}
            for mask in range(1 << n):
                ix = [i for i in range(n) if mask >> i & 1]
                if invertible([rows[i] & mask for i in ix]):
                    value = 0
                    for i in ix:
                        value ^= labels[i]
                    true[value] = min(len(ix), true.get(value, n+1))
            for u in range(4):
                answer = principal_witness(rows, labels, u)
                assert (answer is None) == (u not in true)
                if answer is not None:
                    assert answer.bit_count() == true[u]
    for n in range(3, 11):
        rows = [1 << ((i+1) % n) for i in range(n)]
        rows[0] |= 1
        assert principal_witness(rows, [0,1]+[0]*(n-2), 1) == (1 << n)-1
        assert syndrome_bound(rows, [0,1,1]+[0]*(n-3), 1) == 0
        # Replace one edge in a bidirected cycle by an oriented edge.
        for i in range(1,n):
            rows[i] |= 1 << (i-1)
        assert syndrome_bound(rows, [0,1,1]+[0]*(n-3), 1) <= 2
    print("384 arbitrary-matrix comparisons and 24 long-cycle controls passed")
