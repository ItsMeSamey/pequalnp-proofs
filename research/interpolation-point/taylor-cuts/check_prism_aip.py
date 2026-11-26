from itertools import product, permutations

codes = {2, 3, 4, 5, 6}
sigma = {2: 3, 3: 2, 4: 5, 5: 6, 6: 4}
weights = {v: (-1 if v in (2, 3) else 1) for v in codes}
assert sum(weights.values()) == 1
assert all(weights[v] == weights[sigma[v]] for v in codes)
for perm in permutations(range(3)):
    for flip in range(8):
        def iso(v):
            return sum(((v >> k) & 1) << perm[k] for k in range(3)) ^ flip
        if {iso(v) for v in codes} == codes:
            assert iso(6) == 6
for n in range(5, 14):
    good = 0
    classes = {}
    for a in product(range(2), repeat=n):
        top = list(codes)
        for i, bit in enumerate(a):
            for _ in range(bit + (i == 0)):
                top = [sigma[v] for v in top]
        bottom_ok = sum(a) % 6 == 0
        assert not (bottom_ok and any(x == y for x, y in zip(codes, top)))
        if bottom_ok:
            good += 1
            marks = tuple(int(v == 0 and i != 0) for i, v in enumerate(a))
            key = min(tuple(marks[(s+j*d) % n] for j in range(n))
                      for s in range(n) for d in (-1, 1))
            classes[key] = classes.get(key, 0) + 1
    assert good >= 2 ** (n-5) and max(classes.values()) <= 4*n
    print(n, good, len(classes), max(classes.values()))
