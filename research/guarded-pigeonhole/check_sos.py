"""Exact finite tests of signed cuts, parity localizers and products of clauses."""
from collections import defaultdict
from fractions import Fraction
from itertools import combinations_with_replacement
from random import Random


def subsets(mask):
    part = mask
    while part:
        yield part
        part = (part - 1) & mask
    yield 0


def multiply(p, q):
    product = defaultdict(int)
    for a, coeff in p.items():
        for b, other in q.items():
            product[a ^ b] += coeff * other
    return {a: c for a, c in product.items() if c}


def check_psd(matrix):
    # Exact symmetric elimination. A zero pivot in a PSD matrix has zero row.
    matrix = [[Fraction(x) for x in row] for row in matrix]
    for i, row in enumerate(matrix):
        pivot = row[i]
        assert pivot >= 0
        if pivot == 0:
            assert not any(row[i:])
            continue
        for j in range(i + 1, len(row)):
            ratio = matrix[j][i] / pivot
            if ratio:
                for k in range(j, len(row)):
                    matrix[j][k] -= ratio * row[k]
                    matrix[k][j] = matrix[j][k]


def main():
    # K7,7 with two attached degree-three vertices, one on each side.
    edges = [(u, v) for u in range(7) for v in range(7, 14)]
    edges += [(14, v) for v in (0, 1, 2)] + [(15, v) for v in (7, 8, 9)]
    m = 16
    stars = [sum(1 << e for e, pair in enumerate(edges) if v in pair)
             for v in range(m)]
    charge = 1 << 14
    signs = {}
    expansion = Fraction(len(edges))
    # Complementary vertex sets define the same cut; retain the smaller side.
    cuts = [0] * (1 << m)
    for side in range(1 << m):
        if side:
            point = side & -side
            cuts[side] = cuts[side ^ point] ^ stars[point.bit_length() - 1]
        size = side.bit_count()
        if 0 < size <= m // 2:
            expansion = min(expansion, Fraction(cuts[side].bit_count(), size))
        if size < m // 2:
            signs[cuts[side]] = (-1) ** (side & charge).bit_count()
    degree = (expansion * m).numerator - 1
    degree //= 6 * (expansion * m).denominator
    assert degree >= 7 and 6 * degree < expansion * m

    def moment(f):
        assert f.bit_count() <= 2 * degree
        return signs.get(f, 0)

    # Verify the star identity on every nonzero input moment in range; the
    # translate of a noncut by a cut is always a noncut.
    translations = 0
    for f in signs:
        if f.bit_count() > 2 * degree:
            continue
        for v, star in enumerate(stars):
            if (f ^ star).bit_count() <= 2 * degree:
                assert moment(f ^ star) == moment(f) * (-1) ** ((charge >> v) & 1)
                translations += 1

    local = stars[14] | stars[15]
    singletons = [1 << i for i in range(len(edges))]
    # The two terminals have disjoint stars. Include monomials with both
    # terminal and external variables, plus products related by signed cuts.
    rng = Random(207)
    basis = set(subsets(local))
    for _ in range(70):
        f = sum(rng.sample(singletons, rng.randint(1, degree)))
        basis.add(f)
        for star in stars:
            if (f ^ star).bit_count() <= degree:
                basis.add(f ^ star)
    classes = {}
    pivots = []
    for a in sorted(basis):
        for i, p in enumerate(pivots):
            if moment(a ^ p):
                break
        else:
            i = len(pivots)
            pivots.append(a)
        classes[a] = (i, moment(a ^ pivots[i]))
    for a, b in combinations_with_replacement(basis, 2):
        i, s = classes[a]
        j, t = classes[b]
        assert moment(a ^ b) == (s * t if i == j else 0)

    # A linear clause forbidding c on J has value HammingDistance(x,c)-1.
    # Its spin expansion below is scaled by 2, a positive scalar.
    clauses = []
    for v in (14, 15):
        star = stars[v]
        for c in subsets(star):
            if (c.bit_count() + ((charge >> v) & 1)) % 2 == 0:
                continue
            polynomial = {0: star.bit_count() - 2}
            for bit in singletons:
                if star & bit:
                    polynomial[bit] = 1 if c & bit else -1
            clauses.append((v, c, polynomial))
    qbasis = [0] + [b for b in singletons if b & local] + singletons[:5]
    assert local.bit_count() + 1 <= degree
    shifts = {a ^ b for a in qbasis for b in qbasis}
    # Fourier expansion of each complete assignment indicator on the union.
    weights = {}
    for c in subsets(local):
        for shift in shifts:
            weights[c, shift] = sum(
                (-1) ** (c & f).bit_count() * moment(f ^ shift)
                for f in subsets(local)
            )
        violates = any((c & stars[v]).bit_count() % 2 != ((charge >> v) & 1)
                       for v in (14, 15))
        matrix = [[weights[c, a ^ b] for b in qbasis] for a in qbasis]
        if violates:
            assert all(x == 0 for row in matrix for x in row)
        else:
            check_psd(matrix)

    pairs = 0
    for first, second in combinations_with_replacement(clauses, 2):
        product = multiply(first[2], second[2])
        direct = {s: sum(coef * moment(f ^ s) for f, coef in product.items())
                  for s in shifts}
        for s in shifts:
            mixed = 0
            for c in subsets(local):
                value = 1
                for v, forbidden, _ in (first, second):
                    value *= 2 * (((c & stars[v]) ^ forbidden).bit_count() - 1)
                mixed += value * weights[c, s]
            assert mixed == (1 << local.bit_count()) * direct[s]
        check_psd([[direct[a ^ b] for b in qbasis] for a in qbasis])
        pairs += 1

    print(f'm={m}, h={expansion}, D={degree}; {translations} star translates, '
          f'{len(basis)} Gram indices, {1 << local.bit_count()} union indicators, '
          f'{pairs} clause-product PSD checks')


if __name__ == '__main__':
    main()
