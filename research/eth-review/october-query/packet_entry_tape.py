"""Frozen packet entry over (Z/2^p)[U,V]/(f(U),V^ell), U fastest."""
from dataclasses import dataclass


@dataclass(frozen=True)
class Ring:
    p: int
    f: tuple  # nonleading coefficients of a monic binary polynomial
    ell: int

    def scalar(self, n):
        return (n % (1 << self.p),) + (0,) * (len(self.f) * self.ell - 1)

    def add(self, x, y):
        return tuple((a+b) % (1 << self.p) for a,b in zip(x,y))

    def neg(self, x):
        return tuple((-a) % (1 << self.p) for a in x)

    def mul(self, x, y):
        e = len(self.f)
        out = [0] * len(x)
        for t in range(self.ell):
            lane = [0] * (2*e-1)
            for j in range(t+1):
                for h in range(e):
                    for k in range(e):
                        lane[h+k] += x[j*e+h] * y[(t-j)*e+k]
            for h in reversed(range(e, len(lane))):
                for k, coefficient in enumerate(self.f):
                    lane[h-e+k] -= lane[h]*coefficient
            for h in range(e):
                out[t*e+h] = lane[h] % (1 << self.p)
        return tuple(out)

    def power(self, x, n):
        y = self.scalar(1)
        while n:
            if n & 1:
                y = self.mul(y,x)
            x = self.mul(x,x)
            n >>= 1
        return y


def target_coefficient(ring, affine_rows, beta):
    """Row format = (constant, sparse sequence of (target-index, coefficient))."""
    left = list(beta)
    zero, one = ring.scalar(0), ring.scalar(1)
    total = zero

    def visit(row, product, remaining):
        nonlocal total
        if remaining > len(affine_rows)-row:
            return
        if row == len(affine_rows):
            total = ring.add(total, product)
            return
        const, coeffs = affine_rows[row]
        if const != zero:
            visit(row+1, ring.mul(product,const), remaining)
        for z, coeff in coeffs:
            if left[z] and coeff != zero:
                left[z] -= 1
                visit(row+1,ring.mul(product,coeff),remaining-1)
                left[z] += 1

    visit(0,one,sum(beta))
    return total


def packet_entry(ring, affine_rows, target_exponents, source_sums_and_powers):
    out = target_coefficient(ring,affine_rows,target_exponents)
    for moment, exponent in source_sums_and_powers:
        out = ring.mul(out,ring.power(moment,exponent))
    return out


def canonical_lift(value, p_create, p_work):
    """Every coordinate is intrinsically represented modulo its birth precision."""
    return tuple((v % (1<<p_create)) % (1<<p_work) for v in value)
