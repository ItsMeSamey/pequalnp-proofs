"""Check a two-marker lower bound in squarefree polynomial calculus."""
from collections import Counter
from itertools import combinations


ROWS = (324, 10, 5, 258, 192, 96, 49, 272, 137)
MARKERS = (274, 134)


def eliminate(row, basis, allowed):
    """Reduce on selected columns, inserting a pivot if independent there."""
    while row & allowed:
        pivot = (row & allowed).bit_length() - 1
        if pivot not in basis:
            basis[pivot] = row
            return None
        row ^= basis[pivot]
    return row


def closure(degree, reduced_products):
    n = len(ROWS)
    monomials = [sum(1 << i for i in indices) for k in range(degree + 1)
                 for indices in combinations(range(n), k)]
    index = {m: i for i, m in enumerate(monomials)}
    all_columns = (1 << len(monomials)) - 1
    basis = {}
    for i, row in enumerate(ROWS):
        polynomial = sum(1 << index[(1 << i) | (1 << j)] for j in range(n) if row >> j & 1)
        eliminate(polynomial, basis, all_columns)
    for marker in MARKERS:
        polynomial = 1 + sum(1 << index[1 << j] for j in range(n) if marker >> j & 1)
        eliminate(polynomial, basis, all_columns)
    sizes = [len(basis)]
    while True:
        previous = tuple(basis.values())
        for j in range(n):
            variable = 1 << j
            forbidden = sum(1 << i for i, m in enumerate(monomials)
                            if m.bit_count() == degree and (not reduced_products or not m & variable))
            projected_basis = {}
            for polynomial in previous:
                source = eliminate(polynomial, projected_basis, forbidden)
                if source is None:
                    continue
                product = 0
                while source:
                    bit = source & -source
                    source ^= bit
                    product ^= 1 << index[monomials[bit.bit_length() - 1] | variable]
                eliminate(product, basis, all_columns)
        if len(basis) == sizes[-1]:
            return sizes, 0 in basis
        sizes.append(len(basis))


def check():
    n = len(ROWS)
    assert all(((ROWS[i] >> j) ^ (ROWS[j] >> i)) & 1 == 0
               for i in range(n) for j in range(n))
    counts = Counter(tuple((x & a).bit_count() % 2 for a in MARKERS)
                     for x in range(1 << n)
                     if all(not (x >> i & 1) or (x & row).bit_count() % 2 == 0
                            for i, row in enumerate(ROWS)))
    assert counts == {(0, 0): 10, (0, 1): 10, (1, 0): 8}
    quadratic, refuted = closure(2, True)
    assert not refuted
    cubic, refuted = closure(3, False)
    assert refuted
    print("Quadratic dimensions", quadratic, "cubic dimensions", cubic)


if __name__ == "__main__":
    check()
