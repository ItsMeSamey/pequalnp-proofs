"""Compare the alternating-form recursion with exhaustive subspace enumeration."""
from itertools import combinations
from random import Random

def span(basis):
    points = [0]
    for v in basis:
        points += [x ^ v for x in points]
    return points

def basis_of(points):
    pivots = {}
    for v in points:
        while v:
            i = v.bit_length() - 1
            if i not in pivots:
                pivots[i] = v
                break
            v ^= pivots[i]
    return list(pivots.values())

def hyperplane(n, a):
    pivot = a & -a
    return [(1 << i) ^ (pivot if a & (1 << i) else 0)
            for i in range(n) if 1 << i != pivot]

def width_test(basis, h, tau, exhaustive):
    n = len(basis)
    if not any(tau(*triple) for triple in combinations(basis, 3)):
        return True
    if not h:
        return False
    if exhaustive:
        normals = range(1, 1 << n)
    else:
        pairs = list(combinations(basis, 2))
        contractions = [sum(tau(v, x, y) << j for j, (x, y) in enumerate(pairs))
                        for v in basis]
        images, selected = [], []
        for i, vector in enumerate(contractions):
            if len(basis_of(images + [vector])) > len(images):
                selected.append(basis[i])
                images.append(vector)
        if len(selected) <= h:
            return True
        normals = set()
        for x in span(selected[:h + 1])[1:]:
            rows = [sum(tau(x, y, z) << j for j, z in enumerate(basis))
                    for y in basis]
            independent = basis_of(rows)
            if len(independent) <= 2 * h:
                normals.update(span(independent)[1:])
    ambient = span(basis)
    return any(width_test([ambient[v] for v in hyperplane(n, a)], h - 1,
                          tau, exhaustive) for a in normals)

def run():
    rng = Random(148)
    checks = 0
    for n in range(3, 7):
        basis = [1 << i for i in range(n)]
        triples = list(combinations(range(n), 3))
        for _ in range(5):
            terms = [t for t in triples if rng.randrange(2)]
            def tau(x, y, z):
                bit = 0
                for i, j, k in terms:
                    for a, b, c in ((i,j,k),(i,k,j),(j,i,k),(j,k,i),(k,i,j),(k,j,i)):
                        bit ^= ((x >> a) & (y >> b) & (z >> c) & 1)
                return bit
            for h in range(3):
                assert width_test(basis,h,tau,False) == width_test(basis,h,tau,True)
                checks += 1
    print(checks, 'threshold decisions matched exhaustive subspace search')

if __name__ == '__main__':
    run()
