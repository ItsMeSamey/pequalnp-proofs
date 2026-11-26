"""Exact mincut certificates for successive dirty-gate pins."""
from itertools import repeat

N = 161203
q = 401
k = q + 1
budget = 646425
runs = [(4, 27), (5, 13), (6, 8), (7, 5), (8, 3), (9, 2),
        (10, 2), (11, 1), (12, 1), (13, 1), (14, 1), (17, 1),
        (20, 1), (28, 1)]
z = 0
steps = 0
for degree, count in runs:
    for d in repeat(degree, count):
        m = N - k*z
        assert d <= q-z
        target = budget*d//(d+1) + 1
        assert d*m >= target
        for u in range(max(0, m - target//d), m+1):
            need = target - d*(m-u)
            if need <= 0:
                continue
            # Integer e exceeds need-1 as soon as its mixing lower bound does.
            positive_side = k*m*u - N*(need-1)
            assert positive_side > 0
            assert positive_side**2 > q*m*u*(N-m)*(N-u), (steps, z, d, u)
        z += d-1
        steps += 1
assert (steps, z) == (67, 366)
print(f"{steps} dirty pin rounds certified; final per-side cap {z}")
