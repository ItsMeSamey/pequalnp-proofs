"""Small exhaustive checks for the Jacobian constructions and sparse factoring tests."""
from itertools import combinations, product
from math import gcd


def table_poly(mask):
    v = [(mask >> i) & 1 for i in range(4)]
    return v[0], v[1] - v[0], v[2] - v[0], v[3] - v[2] - v[1] + v[0]


def gate(poly, a, b, mode):
    c, u, v, t = poly
    if mode == "cubic":
        return c + u * a*a + v * b*b + t * (a*a*b + a*b*b - a*b)
    if mode == "quartic":
        a, b = a*a, b*b
    return c + u * a + v * b + t * a*b


def check_roots():
    trials = 0
    for mask in range(16):
        poly = table_poly(mask)
        expect = {(a, b, 1) for a, b in product((0, 1), repeat=2)
                  if gate(poly, a, b, "ordinary") == 1}
        for modulus in (2, 4, 8):
            for mode in ("quadratic", "cubic", "quartic"):
                found = set()
                for a, b, y in product(range(modulus), repeat=3):
                    if (a*a - a + 1 - y*y) % modulus or (b*b - b) % modulus:
                        continue
                    # In the quadratic encoding the auxiliary equations s=w²
                    # have a unique solution for any specified originals.
                    aa, bb = (a*a, b*b) if mode == "quadratic" else (a, b)
                    if (y - gate(poly, aa, bb, mode)) % modulus == 0:
                        found.add((a, b, y))
                assert found == expect
                trials += 1
    return trials


def sparse_counts(m, limit):
    n = 1 << m
    target = (1 << n) + 1
    results = []
    for weight in range(1, limit + 1):
        count = split = 0
        for positions in combinations(range(1, n), weight - 1):
            for signs in product((-1, 1), repeat=weight - 1):
                value = 1 + sum(s * (1 << j) for s, j in zip(signs, positions))
                g = gcd(target, value)
                count += 1
                split += 1 < g < target
        results.append((count, split))
    return results


if __name__ == "__main__":
    trials = check_roots()
    assert sparse_counts(5, 3)[-1][1] == 3
    counts = sparse_counts(6, 4)
    assert counts == [(1, 0), (126, 0), (7812, 0), (317688, 0)]
    assert 1 - (1 << 8) - (1 << 12) + (1 << 14) + (1 << 18) == 274177
    assert gcd(1 + (1 << 64), 274177) == 274177
    print(f"{trials} complete residue-root checks across all 16 binary Boolean gates")
    print("F5 splits at 3 terms; F6 has 325627 failures through 4 and a 5-term split")
