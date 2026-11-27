"""Exact small-system replay. Linear gate forms include the constant at bit 0."""
from itertools import product
from random import Random

def symdiff_product(a, b):
    terms = set()
    for i in range(a.bit_length()):
        if (a >> i) & 1:
            for j in range(b.bit_length()):
                if (b >> j) & 1:
                    terms ^= {(1 << i >> 1) | (1 << j >> 1)}
    return terms

def linear(a):
    return symdiff_product(a, 1)

def gauss(q, dimension):
    active = (1 << dimension) - 1
    factor = 1
    while pair := next((x for x in q if x.bit_count() == 2), 0):
        i = pair & -pair
        j = pair ^ i
        a = {x ^ i for x in q if x & i and not x & j}
        b = {x ^ j for x in q if x & j and not x & i}
        q = {x for x in q if not x & pair}
        for left, right in product(a,b):
            q ^= {left | right}
        factor *= 2
        active ^= pair
    return 0 if q - {0} else factor * (-1 if 0 in q else 1) * (1 << active.bit_count())

def compressed(n, gates, out):
    basis = {}
    def split(row, add=False):
        coords = 0
        for i in sorted(basis, reverse=True):
            if row >> i & 1:
                vec, unit = basis[i]
                row ^= vec
                coords ^= unit
        if row:
            assert add
            unit = 1 << len(basis)
            basis[row.bit_length()-1] = (row, unit)
            coords ^= unit
        return coords
    shift = n+1
    mask = (1 << shift)-1
    for operands in gates:
        for form in operands:
            split(form >> shift, True)
    def operand(form):
        return (form & mask) | (split(form >> shift) << shift)
    polys = [symdiff_product(operand(a), operand(b)) for a,b in gates]
    def substitute(form):
        q = linear(form & mask)
        for i,p in enumerate(polys):
            if form >> (i+shift) & 1:
                q ^= p
        return q
    residuals = [substitute(out ^ 1)]
    for vec, unit in basis.values():
        residuals.append(substitute(vec << shift) ^ linear(unit << shift))
    total = 0
    for character in range(1 << len(residuals)):
        q = set()
        for i,p in enumerate(residuals):
            if character >> i & 1:
                q ^= p
        total += gauss(q, n+len(basis))
    return total // (1 << len(residuals))

def brute(n, gates, out):
    count = 0
    for x in range(1 << n):
        bits = (x << 1) | 1
        for i,(a,b) in enumerate(gates):
            value = ((a & bits).bit_count() & (b & bits).bit_count()) & 1
            bits |= value << (1+n+i)
        count += (out & bits).bit_count() % 2
    return count

if __name__ == '__main__':
    rng = Random(20261127)
    for trial in range(400):
        n,m = rng.randrange(6),rng.randrange(6)
        gates = [tuple(rng.getrandbits(1+n+i) for _ in range(2)) for i in range(m)]
        out = rng.getrandbits(1+n+m)
        assert brute(n,gates,out) == compressed(n,gates,out)
    print('400 exact count comparisons passed')
