"""Verify binary swap corrections in the regular representation."""
from math import comb


def rank(rows):
    pivots = {}
    for x in rows:
        while x:
            idx = x.bit_length()-1
            if idx in pivots:
                x ^= pivots[idx]
            else:
                pivots[idx] = x
                break
    return len(pivots)


def translate(a, shift):
    out = 0
    while a:
        bit = a & -a
        out |= 1 << ((bit.bit_length()-1)^shift)
        a ^= bit
    return out


cases = 0
for h in range(9):
    size = 1 << h
    for R in range(1,h+3):
        g = 0
        for s in range(size):
            if s.bit_count() >= R:
                continue
            sub = s
            while True:
                g ^= 1 << sub
                if sub == 0:
                    break
                sub = (sub-1)&s
        M = translate(g, size-1)
        rk = rank(translate(M^1,i) for i in range(size))
        assert all((i^(size-1)).bit_count() < R for i in range(size) if (M>>i)&1)
        cut = (h-R)//2
        lower = sum(comb(h,i) for i in range(cut+1))
        upper = sum(comb(h,i) for i in range(h+1) if i<=cut or i>=cut+R+1)
        assert lower <= rk <= upper <= 2*lower
        cases += 1
print(cases,"binary orbit rank and support checks passed")
