"""Deterministic slope for Frobenius plus inverse Frobenius over a binary field."""
from field_plane_root import rational_roots
from quadratic_target import insert


def power(field, x, n):
    result = 1
    while n:
        if n & 1:
            result = field.mul(result, x)
        x = field.mul(x, x)
        n >>= 1
    return result


def slope(field):
    """Return c with x -> x² + sqrt(x) + c*x invertible."""
    degree = field.m
    e = 1
    a = 1
    while degree % 3 == 0:
        roots = rational_roots(field, (a, 1, 0, 1))
        if not roots:
            raise ArithmeticError("Dickson descent failed")
        a = min(roots)
        e *= 3
        degree //= 3
    c = power(field, a, -pow(3, -1, (1 << e) - 1) % ((1 << e) - 1)) if e > 1 else 1
    pivots = {}
    for i in range(field.m):
        x = 1 << i
        image = field.mul(x, x) ^ field.sqrt(x) ^ field.mul(c, x)
        if not insert(image, 0, pivots):
            raise ArithmeticError("singular original-coordinate translate")
    return c


if __name__ == "__main__":
    from punctured_witness import BinaryField
    from quadratic_image import field_modulus
    for d in list(range(2, 19)) + [27]:
        f = BinaryField(field_modulus(d))
        c = slope(f)
        if d <= 9:
            assert all(f.mul(x, x) ^ f.sqrt(x) ^ f.mul(c, x) for x in range(1, f.size))
        print(d, c)


def weighted_slope(field, b):
    """Safe slope for b*x²+sqrt(b*x); diagonal scalar shifts can be added."""
    if not b:
        return 1
    # Scale the kernel cubic X³+(c/b)² X+1/b to the unit-constant cubic.
    roots = rational_roots(field, (field.inverse(b), 0, 0, 1))
    if not roots:
        return 0
    return field.mul(field.mul(b, roots[0]), slope(field))
