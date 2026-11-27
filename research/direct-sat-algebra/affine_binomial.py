"""Deterministic feasibility of affine binomial systems in a supplied binary field."""
from sympy import Matrix, eye, zeros
from sympy.matrices.normalforms import hermite_normal_form


def power(field, x, exponent):
    result = 1
    while exponent:
        if exponent & 1:
            result = field.mul(result, x)
        x = field.mul(x, x)
        exponent >>= 1
    return result


def least_support_count(field, n, equations):
    """Return least Boolean support and count on it. Zero count decides infeasibility.

    Equations are pairs of (coefficient, exponent tuple) terms. Zero coefficients
    are accepted, including two zero sides. The fiber count refers only to the
    least support, not to all affine solutions.
    """
    if not isinstance(n, int) or n < 0:
        raise ValueError('invalid dimension')
    rules = []
    pairs = []
    forbidden = []
    for equation in equations:
        terms = []
        for c, powers in equation:
            powers = tuple(powers)
            if not 0 <= c < field.size or len(powers) != n or any(
                    not isinstance(v, int) or v < 0 for v in powers):
                raise ValueError('invalid monomial')
            if c:
                terms.append((c, powers, frozenset(i for i, v in enumerate(powers) if v)))
        if len(equation) != 2:
            raise ValueError('expected two terms')
        if len(terms) == 2:
            a, b = terms
            rules.extend(((a[2], b[2]), (b[2], a[2])))
            pairs.append((a, b))
        elif terms:
            forbidden.append(terms[0][2])
    support = set()
    while True:
        old_size = len(support)
        for left, right in rules:
            if left <= support:
                support.update(right)
        if len(support) == old_size:
            break
    indices = tuple(sorted(support))
    if any(mask <= support for mask in forbidden):
        return indices, 0
    order = field.size - 1
    active = [(a, b) for a, b in pairs if a[2] <= support]
    if not active:
        return indices, order ** len(indices)
    e = len(active)
    matrix = zeros(e, len(indices))
    constants = []
    for row, (a, b) in enumerate(active):
        constants.append(field.mul(b[0], field.inverse(a[0])))
        for j, variable in enumerate(indices):
            matrix[row, j] = (a[1][variable] - b[1][variable]) % order
    # Full-row-rank lattice with known determinant multiple, permitting modular HNF.
    basis = hermite_normal_form(matrix.row_join(order * eye(e)), D=order**e)
    test = order * basis.inv()
    for row in test.tolist():
        product = 1
        for c, coefficient in zip(constants, row):
            assert coefficient.is_Integer
            product = field.mul(product, power(field, c, int(coefficient) % order))
        if product != 1:
            return indices, 0
    return indices, int(order**len(indices) * basis.det() // order**e)


if __name__ == '__main__':
    from itertools import product
    from random import Random
    from punctured_witness import BinaryField
    rng = Random(676621)
    tested = 0
    for modulus in (7, 11):
        field = BinaryField(modulus)
        for n in range(4):
            for trial in range(40):
                def term():
                    return rng.randrange(field.size), tuple(rng.randrange(5) for _ in range(n))
                equations = [(term(), term()) for _ in range(rng.randrange(6))]
                supp, count = least_support_count(field, n, equations)
                all_count = restricted = 0
                for x in product(range(field.size), repeat=n):
                    def evaluate(term):
                        c, exps = term
                        for v, exponent in zip(x, exps):
                            c = field.mul(c, power(field, v, exponent))
                        return c
                    if all(evaluate(a) == evaluate(b) for a, b in equations):
                        all_count += 1
                        restricted += tuple(i for i, v in enumerate(x) if v) == supp
                assert count == restricted and bool(count) == bool(all_count)
                tested += 1
    print(tested, 'least-support counts and global decisions checked')
