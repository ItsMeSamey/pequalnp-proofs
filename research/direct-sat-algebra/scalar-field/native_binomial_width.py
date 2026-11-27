"""Native odd-support controls with one binary-field coordinate and a subfield chart."""
from affine_binomial import power
from punctured_witness import BinaryField


def control(modulus, dimension):
    field = BinaryField(modulus)
    assert field.m % dimension == 0
    size = 2**dimension
    order = field.size - 1
    width = order // (size - 1)
    for x in range(field.size):
        subgroup = power(field, x, size) == x
        if not x:
            assert subgroup
            continue
        indicator = 0
        for j in range(width):
            indicator ^= power(field, x, j*(size-1))
        assert indicator == int(subgroup)
    return field.size, size, width


if __name__ == '__main__':
    for args in ((19, 2), (67, 1), (67, 3), (283, 2), (283, 4)):
        print(control(*args))
