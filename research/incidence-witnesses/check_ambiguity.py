from itertools import combinations

points = list(range(1, 8))
lines = [sum(1 << i for i, p in enumerate(points) if (p & l).bit_count() % 2 == 0)
         for l in points]
unions = lines + [lines[i] | lines[j] for i,j in combinations(range(7),2)]
cols = [sum(1 << x for x in range(128) if x & mask) for mask in unions]
pivots = {}
for col in cols:
    while col and col.bit_length() in pivots:
        col ^= pivots[col.bit_length()]
    if col:
        pivots[col.bit_length()] = col
assert len(pivots) == len(unions) == len(set(unions)) == 28
for truth in range(1 << 16):
    coeff = [(truth >> j) & 1 for j in range(16)]
    for i in range(4):
        for j in range(16):
            if j & (1 << i):
                coeff[j] ^= coeff[j ^ (1 << i)]
    for x in (0,1,2,4,8,3,5,6,9,10,12):
        got = sum(coeff[j] for j in range(16) if (j & x)==j and j.bit_count()<=2) % 2
        assert got == ((truth >> x)&1)
print('28 Fano columns independent over F2; all 65536 small cut aggregators passed')
