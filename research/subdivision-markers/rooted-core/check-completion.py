"""Verify the circuit–cocircuit completion and displayed minors."""
from itertools import product

def rank(rows):
    pivots = {}
    for value in rows:
        while value:
            top = value.bit_length() - 1
            if top not in pivots:
                pivots[top] = value
                break
            value ^= pivots[top]
    return len(pivots)

checked = 0
for a, b in product(range(1, 4), repeat=2):
    for digits in product(range(1<<b), repeat=a):
        n = 2*(a+b)
        C = [1<<i for i in range(n)]
        for i, row in enumerate(digits):
            entries = (row << (2*a)) | (row << (2*a+b))
            C[i] ^= entries
            C[i+a] ^= entries
        assert rank(C) == n
        assert all(row.bit_count()%2 == 1 for row in C)
        assert all(sum(row>>i&1 for row in C)%2 == 1 for i in range(n))
        S = [row | (1<<n) for row in C] + [(1<<n)-1]
        assert rank(S) == n
        assert all(row.bit_count()%2 == 0 for row in S)
        assert all(sum(row>>i&1 for row in S)%2 == 0 for i in range(n+1))
        assert [((row >> (2*a)) & ((1<<b)-1)) for row in S[:a]] == list(digits)
        checked += 1
print(checked, 'binary input matrices, shapes through 3 by 3')
