"""Construct the 12-bit strict ternary fixture and verify its signed CNF directly."""
from itertools import combinations


def pattern(word, scope):
    return sum(((word >> bit) & 1) << j for j, bit in enumerate(scope))


def construct():
    g = 12
    scopes = list(combinations(range(g), 3))
    degree = len(scopes)
    # Use a common denominator 7^degree for every expected survival weight.
    powers = [6**r * 7**(degree-r) for r in range(degree+1)]
    remaining = {}
    for word in range(1, 1 << g):
        zeros = g - word.bit_count()
        remaining[word] = degree - zeros*(zeros-1)*(zeros-2)//6

    formula = []
    for scope in scopes:
        classes = [[] for _ in range(8)]
        scores = [0]*8
        for word, r in remaining.items():
            value = pattern(word, scope)
            if value:
                classes[value].append(word)
                scores[value] += powers[r-1]
        forbidden = max(range(1, 8), key=scores.__getitem__)
        formula.append(tuple(-(bit+1) if forbidden >> j & 1 else bit+1
                             for j, bit in enumerate(scope)))
        for value in range(1, 8):
            for word in classes[value]:
                if value == forbidden:
                    del remaining[word]
                else:
                    remaining[word] -= 1
    return tuple(formula)


def verify(formula):
    scopes = {tuple(sorted(abs(lit) for lit in row)) for row in formula}
    assert len(formula) == 220 and scopes == set(combinations(range(1, 13), 3))
    models = []
    for word in range(4096):
        if all(any(bool(word & (1 << (abs(lit)-1))) == (lit > 0)
                   for lit in row) for row in formula):
            models.append(word)
    assert models == [0]
    return len(formula), tuple(models)


if __name__ == "__main__":
    print(verify(construct()))
