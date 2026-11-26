from itertools import product


# The two perfect matchings of K2,2.
n = 4
matchings = [[(0, 2), (1, 3)], [(0, 3), (1, 2)]]
clauses = []
for s, matching in enumerate(matchings):
    for i, (u, v) in enumerate(matching):
        code = 13 + s * 2 + i
        for a, b in product(range(2), repeat=2):
            clauses.append((code if s == 0 else -code,
                            (1+u) * (1-2*a), (1+v) * (1-2*b),
                            5+u+4*a, 5+v+4*b))
for code in range(13, 16):
    clauses.extend([(-code, code+1), (code, -code-1)])


def sat(bits):
    return all(any(((bits >> (abs(lit)-1)) & 1) == (lit > 0)
                   for lit in clause) for clause in clauses)


count = sum(sat(bits) for bits in range(1 << 16))
assert count == 2**(1+2*n) * 3**(n//2)
for matching in matchings:
    labeled = set()
    for y in product(range(2), repeat=n):
        edges = tuple(tuple((v, y[v]) for v in edge) for edge in matching)
        labeled.add(edges)
    assert len(labeled) == 2**n
print(f'Exhaustive native count {count}; 16 distinct single-class residuals for each code')
