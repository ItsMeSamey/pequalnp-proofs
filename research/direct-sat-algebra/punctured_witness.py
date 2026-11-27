"""Witness x*y=t, Tr(a*x)=Tr(b*y)=1 in a supplied binary field of degree >= 2.

BinaryField(modulus) verifies the packed irreducible polynomial. Call
witness(field,a,b,t); it returns (x,y) or None. Basis and element bits are
polynomial-basis coefficients. The search uses polynomially many bit operations.
"""
from quadratic_image import multiply, remainder
from quadratic_target import affine_domain


class BinaryField:
    def __init__(self, modulus):
        if not isinstance(modulus, int) or modulus < 4:
            raise ValueError("expected a polynomial of degree at least two")
        self.modulus = modulus
        self.m = modulus.bit_length() - 1
        self.size = 1 << self.m
        # Every reducible polynomial has an irreducible factor of degree <= m/2.
        # X^(2^k)-X includes all irreducibles of degree k.
        power = 2
        for _ in range(self.m // 2):
            power = self.mul(power, power)
            f, g = modulus, power ^ 2
            while g:
                f, g = g, remainder(f, g)
            if f != 1:
                raise ValueError("reducible field polynomial")
        self.trace_mask = sum(self._trace(1 << i) << i for i in range(self.m))

    def mul(self, a, b):
        return multiply(a, b, self.modulus)

    def _trace(self, x):
        total = 0
        for _ in range(self.m):
            total ^= x
            x = self.mul(x, x)
        if total not in (0, 1):
            raise ArithmeticError("trace outside prime field")
        return total

    def trace(self, x):
        return (self.trace_mask & x).bit_count() & 1

    def trace_row(self, a):
        return sum(self.trace(self.mul(a, 1 << i)) << i for i in range(self.m))

    def sqrt(self, x):
        for _ in range(self.m - 1):
            x = self.mul(x, x)
        return x

    def inverse(self, x):
        if not x:
            raise ZeroDivisionError
        # x^(2^m-2): after m-1 steps result=x^(2^(m-1)-1).
        result = 1
        for _ in range(self.m - 1):
            result = self.mul(self.mul(result, result), x)
        return self.mul(result, result)


def _linearized(field, coeffs, value):
    out = 0
    for c in coeffs:
        out ^= field.mul(c, value)
        value = field.mul(value, value)
    return out


def reciprocal_sum(field, offset, basis):
    """Sum of reciprocal elements of offset + span(basis), assumed to omit 0."""
    coeffs = [1]  # subspace polynomial for {0} is X
    for v in basis:
        factor = _linearized(field, coeffs, v)
        if not factor:
            raise ValueError("dependent subspace basis")
        nxt = [field.mul(factor, c) for c in coeffs] + [0]
        for j, c in enumerate(coeffs):
            nxt[j + 1] ^= field.mul(c, c)
        coeffs = nxt
    denominator = _linearized(field, coeffs, offset)
    if not denominator:
        raise ValueError("affine space contains zero")
    return field.mul(coeffs[0], field.inverse(denominator))


def witness(field, a, b, t):
    if any(not isinstance(v, int) or not 0 <= v < field.size for v in (a, b, t)):
        raise ValueError("field element outside supplied encoding")
    if not a or not b or not t:
        return None
    d = field.mul(b, t)
    # The c-functional is nonzero by invertibility of multiplication and
    # Frobenius, and nondegeneracy of the absolute trace pairing.
    c = next((1 << j for j in range(field.m)
              if field.trace(field.mul(d, field.sqrt(field.mul(a, 1 << j))))), None)
    if c is None:
        raise ArithmeticError("nonzero trace functional vanished on a basis")
    equations = [(field.trace_row(a), 1), (field.trace_row(c), 1)]

    def odd(slice_equations):
        chart = affine_domain(field.m, slice_equations)
        if chart is None:
            return False
        offset, basis, _ = chart
        return bool(field.trace(field.mul(d, reciprocal_sum(field, offset, basis))))

    if not odd(equations):
        raise ArithmeticError("initial slice has even parity")
    x = 0
    for j in range(field.m):
        bit = 1 << j
        value = int(not odd([*equations, (bit, 0)]))
        equations.append((bit, value))
        x |= value << j
    y = field.mul(t, field.inverse(x))
    if field.mul(x, y) != t or not field.trace(field.mul(a, x)) or not field.trace(field.mul(b, y)):
        raise ArithmeticError("recovered witness failed direct verification")
    return x, y


def check():
    from itertools import product
    checks = 0
    for modulus in (7, 11, 19):
        f = BinaryField(modulus)
        inverse = {a: next(b for b in range(1, f.size) if f.mul(a, b) == 1)
                   for a in range(1, f.size)}
        for a, b, t in product(range(f.size), repeat=3):
            possible = any(f.trace(f.mul(a, x)) and f.trace(f.mul(b, f.mul(t, inv)))
                           for x, inv in inverse.items())
            got = witness(f, a, b, t)
            assert (got is not None) == possible
            if got is not None:
                x, y = got
                assert f.mul(x, y) == t and f.trace(f.mul(a, x)) == f.trace(f.mul(b, y)) == 1
            checks += 1
    for reducible in (4, 5, 9, 15, 21, 27):
        try:
            BinaryField(reducible)
        except ValueError:
            continue
        raise AssertionError("accepted reducible modulus")
    print(f"{checks} exhaustively compared field-product targets and six rejected moduli")


if __name__ == "__main__":
    check()
