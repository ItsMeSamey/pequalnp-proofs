"""Check binary-gate factorization and edge-cover multilinear coefficients."""
from fractions import Fraction
from itertools import permutations, product

for values in product(range(2), repeat=4):
    a, f01, f10, f11 = values
    b, c = f10 - a, f01 - a
    d = f11 - a - b - c
    for u, v in product(range(-2, 3), repeat=2):
        expanded = a + b*u + c*v + d*u*v
        factored = ((d*u+c)*(v+Fraction(b,d))+a-Fraction(b*c,d)
                    if d else a+b*u+c*v)
        assert expanded == factored

for m in range(1, 5):
    row = (1 << m) - 1
    col = sum(1 << (m*i) for i in range(m))
    lines = [row << (m*i) for i in range(m)] + [col << i for i in range(m)]
    coefficients = [int(all(mask & line for line in lines))
                    for mask in range(1 << (m*m))]
    for i in range(m*m):
        bit = 1 << i
        for mask in range(len(coefficients)):
            if mask & bit:
                coefficients[mask] -= coefficients[mask ^ bit]
    matchings = {sum(1 << (m*i+j) for i,j in enumerate(p)) for p in permutations(range(m))}
    assert all(c == int(mask in matchings) for mask,c in enumerate(coefficients)
               if mask.bit_count() <= m)
    print(m, len(coefficients), len(matchings))
