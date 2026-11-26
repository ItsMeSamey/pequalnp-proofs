"""Exhaust the local identities as Boolean functions on independent wire symbols."""
from itertools import product

# Codes are respectively no literal, negative only, positive only, both signs.
def value(code, bit):
    return (1, bit, 1 ^ bit, 0)[code]


local_cases = 0
for c, d in product(range(4), repeat=2):
    for x, s, p, q, S, P, Q in product(range(2), repeat=7):
        zs, zp, zq = value(c | d, x), value(c, x), value(d, x)
        assert zs == zp * zq
        hs, hp, hq = S ^ (s * zs), P ^ (p * zp), Q ^ (q * zq)
        rhs = hs ^ (zs * (s ^ (p*q))) ^ (Q * hp) ^ (p * zp * hq)
        assert rhs == S ^ (P*Q)
        local_cases += 1

resolution_cases = 0
for x, A, B, L, H, R in product(range(2), repeat=6):
    ds, dl, dh = R ^ (A*B), L ^ (A*(1^x)), H ^ (B*x)
    assert R == ds ^ (B*dl) ^ (A*dh) ^ (B*L) ^ (A*H)
    resolution_cases += 1

extension_cases = 0
for u, v in product(range(2), repeat=2):
    g = u*v
    # Falsity values for (¬e∨u), (¬e∨v), and (e∨¬u∨¬v).
    for f in (lambda e: e*(1^u), lambda e: e*(1^v), lambda e: (1^e)*u*v):
        assert not f(g)
        for e in range(2):
            assert f(e) == (f(0)^f(1))*(e^g)
            extension_cases += 1
print(f"{local_cases} prefix identities, {resolution_cases} resolution identities, "
      f"{extension_cases} AND-extension identities verified")
