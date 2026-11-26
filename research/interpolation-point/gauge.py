"""Enumerate twisted symmetric principal-minor signatures on four ports."""
from itertools import combinations_with_replacement
d = 4
pairs = list(combinations_with_replacement(range(d), 2))
def minors(rows):
    determinants = 0
    for mask in range(1 << d):
        basis = {}
        for i in range(d):
            if mask >> i & 1:
                row = rows[i] & mask
                while row and row.bit_length() in basis:
                    row ^= basis[row.bit_length()]
                if row:
                    basis[row.bit_length()] = row
        determinants |= (len(basis) == mask.bit_count()) << mask
    return determinants
def twist(f, t):
    return sum(((f >> (s ^ t)) & 1) << s for s in range(16))
catalogue = {0}
for m in range(1 << len(pairs)):
    rows = [0] * d
    for j, (a, b) in enumerate(pairs):
        if m >> j & 1:
            rows[a] |= 1 << b
            rows[b] |= 1 << a
    f = minors(rows)
    catalogue.update(twist(f, t) for t in range(16))
for f in catalogue:
    for i in range(d):
        mask = sum(1 << s for s in range(16) if s >> i & 1)
        assert twist(f, 1 << i) in catalogue
        assert (f ^ ((f << (1 << i)) & mask)) in catalogue
assert (1 << 3 | 1 << 12) not in catalogue
print(len(catalogue), "signatures closed under all one-port invertible gauges")
