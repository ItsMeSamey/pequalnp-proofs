"""Enumerate physical assignments directly on the two-clause controls."""
from itertools import product


def check(clauses):
    m = len(clauses)
    h = 1 << (m - 1).bit_length()
    p = h * h
    triples = [(p+x, 2*p+y, 3*p+(x^y)) for x,y in product(range(p),repeat=2)]
    assert all(a < b < c and a^b == c for a,b,c in triples)
    assert {(a,b) for a,b,c in triples} == set(product(range(p,2*p),range(2*p,3*p)))
    literals = {}
    for i, clause in enumerate(clauses):
        literals.update(zip((p+i*h, 2*p+i, 3*p+i*h+i),clause))
    first = {}
    for port, lit in literals.items():
        first.setdefault(abs(lit), (port,lit<0))
    witnesses = []
    for bits in product(range(2), repeat=3*p):
        def val(port):
            return bits[port-p]
        if any(not val(j) for j in range(p,4*p) if j not in literals):
            continue
        if any((val(port) ^ (lit<0)) != (val(first[abs(lit)][0]) ^ first[abs(lit)][1])
               for port,lit in literals.items()):
            continue
        if all(val(a) or val(b) or val(c) for a,b,c in triples):
            witnesses.append(tuple(val(first[j][0]) ^ first[j][1] for j in sorted(first)))
    expected = [assignment for assignment in product(range(2),repeat=len(first))
                if all(any(dict(zip(sorted(first),assignment))[abs(l)] ^ (l<0) for l in c) for c in clauses)]
    assert sorted(witnesses) == sorted(expected)
    return len(witnesses)


if __name__ == '__main__':
    cases = [[(1,1,1),(-1,-1,-1)], [(1,2,-1),(-2,-2,-2)], [(1,2,3),(-1,-2,-3)], [(-1,-1,-1)]]
    print('Original witness multiplicities checked:', [check(c) for c in cases])
