"""Exact Walsh products and signed exceptional selectors against direct SAT."""
from collections import defaultdict
from fractions import Fraction
from itertools import combinations, product
from random import Random


def holds(clause,x):
    mask,forbidden = clause
    return (x&mask)!=forbidden


def components(clauses):
    parts = []
    for c in clauses:
        common = [p for p in parts if any(c[0]&a[0] for a in p)]
        parts = [p for p in parts if p not in common]+[[c]+[a for p in common for a in p]]
    return parts


def submasks(m):
    u=m
    while True:
        yield u
        if not u:
            break
        u=(u-1)&m


def spectrum(group):
    variables = 0
    for m,b in group:
        variables |= m
    points = list(submasks(variables))
    return {s:Fraction(sum((-1)**((s&x).bit_count()) for x in points
                            if all(holds(c,x) for c in group)),len(points)) for s in points}


def parity_cnf(n,s,extra,odd):
    clauses = []
    # Forbid (selector=true, literal=true), one binary clause per occurrence.
    for j,(mask,forbidden) in enumerate(extra):
        y = 1<<(n+j)
        for i in range(n):
            x = 1<<i
            if x&mask:
                clauses.append((x|y,y|(0 if forbidden&x else x)))
    wires = [i for i in range(n) if s>>i&1]+list(range(n,n+len(extra)))
    size = n+len(extra)
    if not wires:
        return clauses + ([(0,0)] if odd else []),size
    acc = wires[0]
    for v in wires[1:]:
        t = size
        size += 1
        for a,b in product((0,1),repeat=2):
            clauses.append(((1<<acc)|(1<<v)|(1<<t),(a<<acc)|(b<<v)|((1^a^b)<<t)))
        acc = t
    clauses.append((1<<acc,(1^odd)<<acc))
    return clauses,size


def compute(n,core,long,extra):
    coeffs = {0:Fraction(1)}
    for group in components(long):
        merged = defaultdict(Fraction)
        for b,v in spectrum(group).items():
            if v:
                for a,w in coeffs.items():
                    merged[a^b] += v*w
        coeffs = {a:w for a,w in merged.items() if w}
    direct = sum(all(holds(c,x) for c in core+long+extra) for x in range(1<<n))
    total = 0
    for s,w in coeffs.items():
        counts = [0,0]
        for x,y in product(range(1<<n),range(1<<len(extra))):
            if all(holds(c,x) for c in core) and all(
                    not(y>>i&1) or not holds(c,x) for i,c in enumerate(extra)):
                parity = ((x&s).bit_count()+y.bit_count())%2
                counts[parity] += 1
        if n<=2 and len(extra)<=2:
            for odd in (0,1):
                cnf,size = parity_cnf(n,s,extra,odd)
                assert sum(all(holds(c,x) for c in core+cnf) for x in range(1<<size)) == counts[odd]
        a = counts[0]-counts[1]
        assert a==sum((-1)**((s&x).bit_count()) for x in range(1<<n)
                      if all(holds(c,x) for c in core+extra))
        total += w*a
    assert total == direct
    for x in range(1<<n):
        assert sum(w*(-1)**((s&x).bit_count()) for s,w in coeffs.items())==all(holds(c,x) for c in long)


if __name__=='__main__':
    rng = Random(314159)
    cases = 0
    for n in range(5):
        universe = [(m,b) for m,b in product(range(1<<n),repeat=2) if m&b==b]
        for _ in range(80):
            groups = [rng.choices(universe,k=rng.randrange(4)) for _ in range(3)]
            compute(n,*groups)
            cases += 1
    # Linked short core, two disjoint Walsh groups, and an unused fifth variable.
    compute(5,[(6,2)],[(3,0),(1,1),(12,4)],[(9,1),(10,2)])
    print(cases+1,'combined Walsh-selector instances passed')
