"""Exhaustive two-bit signed lines, checked against direct truth-table Walsh."""
from fractions import Fraction
from itertools import product
from random import Random
from affine_cell_energy import AffineCellEnergy, dot


def check(n, terms, queries):
    engine = AffineCellEnergy(n, terms)
    def belongs(x, eq):
        return all(dot(x, a) == b for a, b in eq)
    values = [sum(w for w, eq in terms if belongs(x, eq)) for x in range(1 << n)]
    spectra = [sum((-1)**dot(s, x) * v for x, v in enumerate(values)) for s in range(1 << n)]
    for query in queries:
        assert engine.energy(query) == sum(v*v for s,v in enumerate(spectra) if belongs(s,query))
    basis = engine.interface()
    actual = {0}
    for v in basis:
        assert v not in actual and spectra[v] != 0
        actual |= {a ^ v for a in actual}
    expected = {0}
    for v, coeff in enumerate(spectra):
        if coeff:
            expected |= {a ^ v for a in expected}
    assert actual == expected
    for t in range(1 << n):
        assert all(not dot(t,v) for v in basis) == all(values[x]==values[x^t] for x in range(1 << n))


if __name__ == '__main__':
    cases = queries_checked = 0
    lines = [((a,b),) for a in (1,2,3) for b in (0,1)]
    queries = [(), ((0,1),)] + lines + [((1,x),(2,y)) for x,y in product(range(2),repeat=2)]
    for weights in product((-1,0,1),repeat=6):
        check(2, list(zip(weights,lines)), queries)
        cases += 1
        queries_checked += len(queries)
    rng = Random(75603)
    for n in range(6):
        def random_cell():
            return tuple((rng.randrange(1<<n), rng.randrange(2)) for _ in range(rng.randrange(n+3)))
        for _ in range(30):
            terms = [(Fraction(rng.randrange(-4,5),rng.randrange(1,5)), random_cell()) for _ in range(8)]
            queries = [()] + [random_cell() for _ in range(12)]
            check(n,terms,queries)
            cases += 1
            queries_checked += len(queries)
    print(cases, 'signed mixtures;', queries_checked, 'frequency energies; all interfaces and periods verified')
