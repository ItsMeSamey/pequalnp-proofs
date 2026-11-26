"""Finite controls for pointer restrictions, scalar shifts and slot averaging."""
from itertools import product

for k in (1, 2, 3):
    t = 2**k
    seen = set()
    for data in product((0, 1), repeat=t):
        seen.add(tuple(data[sum(bit << b for b, bit in enumerate(word))]
                       for word in product((0, 1), repeat=k)))
    assert len(seen) - 2 == 2**t - 2

for values in product(range(-3, 4), repeat=3):
    shifts = set.intersection(*[{0-v, 1-v} for v in values])
    if len(set(values)) > 1:
        assert len(shifts) <= 1

for counts in product(range(3), repeat=6):
    total = sum(sum(counts[2*j+p] for j,p in enumerate(slots))
                for slots in product(range(2), repeat=3))
    assert total == 4 * sum(counts)
print('ISA k=1,2,3; 343 shift tables; 729 slot arrays passed')
