"""Check the selector and signed-block family from strict.md."""
from collections import Counter
from itertools import combinations, product


def construction(r, t):
    blocks = [tuple(range(2+i*t, 2+(i+1)*t)) for i in range(2*r)]
    clauses = []
    for i, block in enumerate(blocks):
        for marked in block:
            clauses.append(frozenset([1 if i < r else -1] +
                                      [-v if v == marked else v for v in block]))
    return blocks, clauses


def check(r, t, exhaustive=False):
    blocks, clauses = construction(r, t)
    n = 1 + 2*r*t
    occurrence = Counter(abs(lit) for c in clauses for lit in c)
    assert [v for v, count in occurrence.items() if count == len(clauses)] == [1]
    assert set().union(*clauses) == set(range(1, n+1)) | set(range(-n, 0))
    assert len(set(clauses)) == len(clauses)
    assert all(len(c) == t+1 == len(set(map(abs, c))) for c in clauses)
    for a, b in combinations(clauses, 2):
        assert len(a ^ b) != 2
    for selector, active in [(False, blocks[:r]), (True, blocks[r:])]:
        restricted = [c - {1,-1} for c in clauses if (1 if selector else -1) not in c]
        assert len(restricted) == r*t
        for block in active:
            local = [c for c in restricted if set(map(abs, c)) == set(block)]
            assert len(local) == t  # incidence K_{t,t} witness
            for assignment in product([False, True], repeat=t):
                literals = {v if flag else -v for v, flag in zip(block, assignment)}
                assert sum(c.isdisjoint(literals) for c in local) == (sum(assignment) == 1)
        for flags in product([False, True], repeat=r):
            true = {block[0] for block, flag in zip(active, flags) if flag}
            violated = [c for c in restricted if all((abs(v) in true) != (v > 0) for v in c)]
            assert len(violated) == sum(flags)
            assert {v for c in violated for v in c if v < 0} == {-v for v in true}
    if exhaustive:
        masks = [(sum(1 << (abs(v)-1) for v in c), sum(1 << (-v-1) for v in c if v<0)) for c in clauses]
        models = sum(all(bits & mask != forbidden for mask, forbidden in masks) for bits in range(2**n))
        assert models == 2 * 2**(t*r) * (2**t-t)**r
        return models


if __name__ == '__main__':
    for r in range(2, 6):
        for t in range(3, 7):
            models = check(r, t, exhaustive=(r,t) in {(2,3),(2,4),(3,3)})
            print(r,t,'structural checks passed',models if models else '')
