"""Deterministic local Tanner components for the native sparse-check controller."""
from functools import lru_cache

@lru_cache(None)
def modulus(degree):
    if degree < 1:
        raise ValueError("positive field degree required")
    for polynomial in range((1 << degree) + 1, 1 << (degree + 1), 2):
        for d in range(1, degree // 2 + 1):
            for divisor in range((1 << d) + 1, 1 << (d+1), 2):
                rem = polynomial
                while rem.bit_length() >= divisor.bit_length():
                    rem ^= divisor << (rem.bit_length() - divisor.bit_length())
                if rem == 0:
                    break
            else:
                continue
            break
        else:
            return polynomial
    raise ArithmeticError("irreducible polynomial unavailable")

def multiply(x, y, mod):
    result = 0
    degree = mod.bit_length() - 1
    while y:
        if y & 1:
            result ^= x
        y >>= 1
        x <<= 1
        if x >> degree:
            x ^= mod
    return result

def distance_matrix(d, c, h):
    if h == 0:
        return (0,) * c
    degree = max(1, (d-1).bit_length())
    if h * degree > c:
        raise ValueError("Vandermonde check exceeds available rows")
    mod = modulus(degree)
    rows = [0] * c
    for x in range(d):
        power = 1
        for k in range(h):
            for bit in range(degree):
                if (power >> bit) & 1:
                    rows[k*degree+bit] |= 1 << x
            power = multiply(power,x,mod)
    return tuple(rows)

def cayley_shifts(d, q, denominator):
    if q < 1 or q & (q-1) or denominator < 1:
        raise ValueError("invalid group or potential")
    if q == 1:
        return (0,) * d
    D = denominator
    # Scale all live +/- exponential weights by [D(D+1)] per step.
    positive = [1] * (q-1)
    negative = positive.copy()
    shifts = []
    for _ in range(d):
        # Every candidate has the same common part; minimize the signed difference.
        diff = [0] + [u-v for u,v in zip(positive,negative)]
        length = 1
        while length < q:
            for start in range(0,q,2*length):
                for j in range(start,start+length):
                    a,b = diff[j],diff[j+length]
                    diff[j],diff[j+length] = a+b,a-b
            length *= 2
        choice = min(range(q),key=diff.__getitem__)
        shifts.append(choice)
        for j in range(q-1):
            up = not ((choice & (j+1)).bit_count() & 1)
            positive[j] *= (D+1)**2 if up else D**2
            negative[j] *= D**2 if up else (D+1)**2
    return tuple(shifts)

def distance_rows(n,m,B):
    mu = m.bit_length()
    P = 20000*B*B*mu*mu
    if m <= P:
        return [],P
    d = min(m,320000*B*B*mu**3)
    q = 1 << (((m+d-1)//d)-1).bit_length()
    shifts = cayley_shifts(d,q,200*B*mu)
    mat = distance_matrix(d,(d+8*B-1)//(8*B),(d-1)//(100*B*mu))
    rows = []
    for side in (0,1):
        for u in range(q):
            for mask in mat:
                row = tuple((idx,1) for j in range(d) if mask>>j&1
                            and (idx := (u if side==0 else u^shifts[j])*d+j) < m)
                if row:
                    rows.append(row)
    assert len(rows)<=3*n
    return rows,P
