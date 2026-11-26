from fractions import Fraction
from itertools import combinations
from math import prod

def v2(x):
    return (abs(x) & -abs(x)).bit_length() - 1

checks = 0
for size in range(1, 9):
    for sites in combinations(range(8), size):
        order = []
        coeffs = []
        norms = []
        for k in range(size):
            differences = {j: prod(j - a for a in order) for j in sites if j not in order}
            j = min(differences, key=lambda j: v2(differences[j]))
            norms.append(2 ** v2(differences[j]))
            order.append(j)
        for i in range(3):
            H = 2 ** (i + 1)
            for val in range(i + 1):
                d = 17 * 2 ** val
                c = 2 ** (i + 1)
                coeffs = [Fraction(c * H**k * norm, prod(d - H*a for a in order[:k+1]))
                          for k,norm in enumerate(norms)]
                for j in sites:
                    result = 0
                    for k, (norm, coeff) in enumerate(zip(norms, coeffs)):
                        numerator = prod(j - a for a in order[:k])
                        assert numerator % norm == 0
                        assert v2(coeff.numerator) - v2(coeff.denominator) >= 1 + k + v2(norm)
                        result += coeff * (numerator // norm)
                    assert result == Fraction(c, d-H*j)
                    checks += 1
print(checks, 'occupied-site rational kernels verified')
