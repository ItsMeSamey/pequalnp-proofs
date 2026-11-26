"""Small truth-table checks for the circuit notes."""
from collections import Counter
from itertools import combinations, product

def parity(mask):
    return mask.bit_count() % 2

def semantic_example(n):
    coords = [sum(((i >> j) & 1) << i for i in range(1 << n)) for j in range(n)]
    count = 1 << (1 << n)
    rows = [[0 if f in coords else f >> (1 << j) & 1 for f in range(count)] for j in range(n)]
    xor = max(sum((r[a] ^ r[b]) != r[a ^ b] for r in rows) for a in range(count) for b in range(count))
    conj = max(sum((r[a] & r[b]) != r[a & b] for r in rows) for a in range(count) for b in range(count))
    assert xor == 2 and conj <= 2 and all(r[count - 2] for r in rows)
    return xor, conj

def multiply(a, b):
    result = 0
    for _ in range(5):
        if b & 1:
            result ^= a
        b >>= 1
        a <<= 1
        if a & 32:
            a ^= 0b100101
    return result

def trace(a):
    total = 0
    for _ in range(5):
        total ^= a
        a = multiply(a, a)
    assert total in (0, 1)
    return total

def masks():
    freq = Counter()
    for u in range(32):
        for v in range(32):
            power = 1
            table = 0
            for i in range(4):
                table |= trace(multiply(u, power)) << i
                power = multiply(power, v)
            freq[table] += 1
    total = sum(freq.values())
    biases = [abs(sum((1 - 2 * parity(w & a)) * count for a, count in freq.items())) for w in range(1, 16)]
    assert max(biases) <= 3 * total // 32
    counts = []
    for h in range(16):
        if h.bit_count() < 2:
            continue
        bad = sum(am * bm for a, am in freq.items() for b, bm in freq.items()
                  if parity(h & a & b) != (parity(h & a) * parity(h & b)))
        counts.append(bad)
    assert min(counts) * 512 >= total ** 2 * 147
    return max(biases), total, min(counts), total ** 2

def hazard():
    # 0=false, 1=unknown, 2=true. AND=min, OR=max, NOT=2-value.
    edges = list(combinations(range(4), 2))
    triangles = [[edges.index(e) for e in combinations(vs, 2)] for vs in combinations(range(4), 3)]
    def baseline(values):
        return max(min(values[i] for i in t) for t in triangles)
    def modified(values):
        poison = max(min(values[i], 2 - values[i]) for i, edge in enumerate(edges) if 0 in edge)
        return max(poison, baseline(values))
    for values in product((0, 2), repeat=6):
        assert baseline(values) == modified(values)
    for partner in range(1, 4):
        side = {0, partner}
        values = [int((i in side) != (j in side)) for i, j in edges]
        assert baseline(values) == 0 and modified(values) == 1

def filters():
    edges = list(combinations(range(4), 2))
    matchings = [(0, 5), (1, 4), (2, 3)]
    triangles = [sum(1 << edges.index(e) for e in combinations(vs, 2)) for vs in combinations(range(4), 3)]
    negatives = [63 ^ ((1 << a) | (1 << b)) for a, b in matchings]
    for t in range(1, 4):
        def passes(g):
            return all(g & ((1 << a) | (1 << b)) for a, b in matchings[:t])
        assert all(passes(g) for g in triangles)
        assert sum(not passes(g) for g in negatives) == t
        essential = sum(any(passes(g) != passes(g ^ (1 << j)) for g in range(64)) for j in range(6))
        assert essential == 2 * t
    assert passes(7)

def width_one():
    edges = list(combinations(range(4), 2))
    triangles = [[edges.index(e) + 1 for e in combinations(vs, 2)] for vs in combinations(range(4), 3)]
    matchings = [(1, 6), (2, 5), (3, 4)]
    base = [set(range(7, 11))] + [{-w, e} for w, tri in enumerate(triangles, 7) for e in tri]
    def width(clauses, missing):
        active = [c - missing for c in clauses if not any(-e in c for e in missing)]
        single = {next(iter(c)) for c in active if len(c) == 1}
        return 0 if set() in active else 1 if any(-s in single for s in single) else 2
    for t in range(4):
        direct = base + [set(m) for m in matchings[:t]]
        split = base + [c for u, (a, b) in enumerate(matchings[:t], 11) for c in ({a, u}, {b, -u})]
        assert [width(direct, set(m)) for m in matchings] == [0] * t + [2] * (3 - t)
        assert [width(split, set(m)) for m in matchings] == [1] * t + [2] * (3 - t)

if __name__ == "__main__":
    for n in (2, 3):
        print("maximum XOR/AND failures across n samples", n, semantic_example(n))
    print("max bias and min nonsingleton rejection as numerator, denominator", masks())
    hazard()
    print("K4 triangle test passed all 64 graphs and 3 balanced negative partial inputs")
    filters()
    print("K4 filters with 1, 3, 5 gates reject 1, 2, 3 negatives and use 2, 4, 6 essential bits")
    width_one()
    print("width-zero and width-one clause constructions checked on all K4 balanced masks")
