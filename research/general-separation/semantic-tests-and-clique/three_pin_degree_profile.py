"""Compute static and iterative proof ranks on a seven-bit binary pin slice."""
from module_affine_escape import affine

GRAPH = [6372,1572,4107,1828,640,8011,161,3665,1064,4282,6570,1185,1573]
PINS = (8,9,10)


def insert(basis, word):
    while word and word.bit_length() in basis:
        word ^= basis[word.bit_length()]
    if word:
        basis[word.bit_length()] = word


def check():
    pin_mask = sum(1 << i for i in PINS)
    free = [i for i in range(len(GRAPH)) if i not in PINS]
    pin_rows = [(sum((GRAPH[i] >> j & 1) << k for k,j in enumerate(free)),
                 (GRAPH[i] & pin_mask).bit_count() % 2) for i in PINS]
    origin, directions = affine(pin_rows,len(free))
    n = len(directions)
    assert n == 7
    monomials = sorted(range(1 << n),key=lambda s:(s.bit_count(),s))
    index = {m:i for i,m in enumerate(monomials)}

    def raw(point):
        z = origin
        for i,v in enumerate(directions):
            if point >> i & 1:
                z ^= v
        return pin_mask | sum((z >> k & 1) << j for k,j in enumerate(free))

    def multiply(poly, monomial):
        value = 0
        while poly:
            j = (poly & -poly).bit_length()-1
            poly &= poly-1
            value ^= 1 << index[monomials[j] | monomial]
        return value

    points = [raw(u) for u in range(1 << n)]
    assert len(set(points)) == 128 and all(
        any((w >> i & 1) and (w & GRAPH[i]).bit_count()%2 for i in free) for w in points)
    guards = []
    for i in free:
        values = [(w >> i & 1) * ((w & GRAPH[i]).bit_count()%2) for w in points]
        for t in range(n):
            for u in range(1 << n):
                if u >> t & 1:
                    values[u] ^= values[u ^ (1 << t)]
        guards.append(sum(values[u] << index[u] for u in range(1 << n)))

    profile = []
    for degree in (2,3,4):
        basis = {}
        for p in guards:
            for m in monomials:
                if m.bit_count() <= degree-2:
                    insert(basis,multiply(p,m))
        static = len(basis), 1 in basis
        while True:
            old = len(basis)
            low = [v for v in basis.values() if monomials[v.bit_length()-1].bit_count() < degree]
            for v in low:
                for i in range(n):
                    insert(basis,multiply(v,1 << i))
            if len(basis) == old:
                break
        profile.append((degree,static,(len(basis),1 in basis)))
    assert profile == [(2,(9,False),(9,False)),(3,(52,False),(64,True)),
                       (4,(99,True),(99,True))]
    return profile


if __name__ == '__main__':
    print(check())
