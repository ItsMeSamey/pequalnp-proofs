"""Exact rational row skeletons and signed digit-count reconstruction."""
from collections import Counter
from itertools import product
from math import prod
from random import Random

from sympy import Matrix


def index(assignment, scope):
    out = 0
    for variable in scope:
        out = 2 * out + assignment[variable]
    return out


def make_train(table, scope, block_size):
    if len(scope) <= block_size or not any(table):
        return [], (scope, table)
    rows = [table]
    layers = []
    for offset in range(0, len(scope), block_size):
        block = scope[offset:offset + block_size]
        width = 2 ** (len(scope) - offset - len(block))
        children = Matrix([row[j:j + width] for row in rows
                           for j in range(0, len(row), width)])
        selected = children.T.rref()[1]
        basis = children[list(selected), :]
        columns = basis.rref()[1]
        minor = basis[:, list(columns)]
        denominator = abs(int(minor.det()))
        weights = children[:, list(columns)] * minor.inv() * denominator
        assert all(x.is_Integer for x in weights)
        assert weights * basis == denominator * children
        rank = len(selected)
        assert denominator ** 2 <= rank ** rank
        assert all(int(x)**2 <= rank**rank for x in weights)
        layers.append((block, denominator, weights.tolist()))
        rows = basis.tolist()
    assert rows == [[1]]
    return layers, None


def digit_positions(integer):
    return [j for j in range(abs(integer).bit_length()) if abs(integer) >> j & 1]


def counts(train, assignment):
    layers, direct = train
    if direct is not None:
        scope, table = direct
        return Counter({(0, 0): table[index(assignment, scope)]})
    states = Counter({(0, 0, 0): 1})
    for block, _, weights in layers:
        after = Counter()
        code = index(assignment, block)
        for (src, parity, exponent), count in states.items():
            for dst, w in enumerate(weights[src * 2**len(block) + code]):
                w = int(w)
                for digit in digit_positions(w):
                    after[dst, parity ^ (w < 0), exponent + digit] += count
        states = after
    return Counter({(p, e): count for (_, p, e), count in states.items()})


def signed_value(hist):
    return sum((-1)**p * 2**e * count for (p, e), count in hist.items())


def check(n, specs):
    trains = [make_train(table, scope, size) for scope, table, size in specs]
    denominator = prod(d for layers, _ in trains for _, d, _ in layers)
    result = Counter()
    models = 0
    for x in product(range(2), repeat=n):
        combined = Counter({(0, 0): 1})
        for train in trains:
            terms = counts(train, x)
            next_terms = Counter()
            for (p, e), count in combined.items():
                for (q, f), multiplicity in terms.items():
                    next_terms[p ^ q, e + f] += count * multiplicity
            combined = next_terms
        truth = prod(table[index(x, scope)] for scope, table, _ in specs)
        assert signed_value(combined) == truth * denominator
        models += truth
        result.update(combined)
    assert signed_value(result) == denominator * models
    return trains, models, denominator, result


def balanced_sum(digits, width):
    work = [[(v >> i) & 1 for i in range(width)] for v in digits]
    cells = 0
    while len(work) > 1:
        next_level = []
        for offset in range(0, len(work)-1, 2):
            left, right = work[offset:offset+2]
            carry, bits = 0, []
            for i in range(max(len(left), len(right))):
                a = left[i] if i < len(left) else 0
                b = right[i] if i < len(right) else 0
                bits.append(a ^ b ^ carry)
                carry = (a & b) | (a & carry) | (b & carry)
                cells += 1
            next_level.append(bits + [carry])
        if len(work) % 2:
            next_level.append(work[-1])
        work = next_level
    return sum(bit << i for i, bit in enumerate(work[0])), cells


def main():
    # Determinant-two 0/1 minor, followed by a row with half-integral coordinates.
    table = [1, 1, 0, 0, 1, 0, 1, 0, 0, 1, 1, 0, 1, 0, 0, 0]
    specs = [(list(range(4)), table, 2), ([3, 1, 0, 2], table, 2),
             ([1], [1, 1], 2)]
    trains, models, denominator, hist = check(4, specs)
    assert denominator == 4 and trains[-1][0] == []
    assert any(p and c for (p, _), c in hist.items())
    assert any(e and c for (_, e), c in hist.items())
    # An independent signed product with multiple enabled digit choices per edge.
    terms = Counter((1, i+j) for i in digit_positions(-13) for j in digit_positions(7))
    assert signed_value(terms) == -91
    rng = Random(712)
    for width in range(1, 9):
        for t in range(1, 65):
            digits = [rng.randrange(2**width) for _ in range(t)]
            value, cells = balanced_sum(digits, width)
            assert value == sum(digits) and cells <= 2*t*(width+1)
    for n in range(3, 8):
        for _ in range(6):
            cases = []
            for _ in range(3):
                scope = rng.sample(range(n), rng.randrange(1, n+1))
                cases.append((scope, [rng.randrange(2) for _ in range(2**len(scope))],
                              rng.randrange(1, 4)))
            check(n, cases)
    check(3, [([0, 1, 2], [0]*8, 1), ([], [1], 2)])
    print(f"32 formula cases passed; fractional example: models={models}, "
          f"denominator={denominator}, signed numerator={signed_value(hist)}")


if __name__ == '__main__':
    main()
