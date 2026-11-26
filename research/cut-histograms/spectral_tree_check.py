"""Exhaustively check the distinguished-field representative DP on small cubes."""
from collections import defaultdict
from functools import cache
import random


class Echelon:
    def __init__(self, p):
        self.p = p
        self.pivots = {}

    def add(self, vector):
        v = list(vector)
        for j, row in sorted(self.pivots.items()):
            if v[j]:
                scale = v[j]
                v = [(a - scale*b) % self.p for a, b in zip(v, row)]
        j = next((j for j, value in enumerate(v) if value), None)
        if j is None:
            return False
        scale = pow(v[j], -1, self.p)
        self.pivots[j] = [x * scale % self.p for x in v]
        return True


def local_columns(f, mask, p):
    rows = sorted({a & mask for a in f})
    outside = sorted({a & ~mask for a in f})
    base = Echelon(p)
    cols = []
    for z in outside:
        col = tuple(f.get(a | z, 0) for a in rows)
        if base.add(col):
            cols.append(tuple(zip(rows, col)))
    return cols


def evaluate(x, terms, p):
    return sum((-c if (x & a).bit_count()%2 else c) for a, c in terms) % p


def check(n, factors, rng):
    pstar = factors[0][0]
    full = (1 << n)-1
    @cache
    def cols(mask):
        return [local_columns(f, mask, p) for p, f in factors]
    @cache
    def signature(mask, x):
        return tuple(tuple(evaluate(x, col, p) for col in c)
                     for (p, _), c in zip(factors, cols(mask)))

    def contract(mask):
        bits = [1 << j for j in range(n) if mask & (1 << j)]
        if len(bits) == 1:
            candidates = [0, mask]
        else:
            rng.shuffle(bits)
            left = sum(bits[:rng.randrange(1, len(bits))])
            a = contract(left)
            b = contract(mask ^ left)
            candidates = [x|y for x in a for y in b]

        bases = defaultdict(lambda: Echelon(pstar))
        kept = []
        for x in candidates:
            star, *rest = signature(mask, x)
            if bases[tuple(rest)].add(star):
                kept.append(x)
        # Independently verify containment for *every* assignment and state.
        for x in range(full+1):
            if x & ~mask:
                continue
            star, *rest = signature(mask, x)
            assert not bases[tuple(rest)].add(star), (mask, x, factors)
        return kept

    kept = contract(full)
    def accepts(x):
        return all(evaluate(x, f.items(), p) for p, f in factors)
    assert any(map(accepts, kept)) == any(map(accepts, range(full+1)))


if __name__ == '__main__':
    rng = random.Random(872149)
    for _ in range(240):
        n = rng.randrange(1, 8)
        factors = []
        for _ in range(rng.randrange(1, 5)):
            p = rng.choice((3, 5, 7))
            size = rng.randrange(min(30, 1 << n)+1)
            f = {a:rng.randrange(1, p) for a in rng.sample(range(1 << n), size)}
            factors.append((p, f))
        check(n, factors, rng)
    print('240 mixed-field trees: all subtree spans and root decisions matched')
