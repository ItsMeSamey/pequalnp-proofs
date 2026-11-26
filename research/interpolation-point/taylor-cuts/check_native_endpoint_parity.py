"""Direct exact audit of packet content and the endpoint NAND construction.

Run with python3 check_native_endpoint_parity.py. Polynomial coefficients use
one fixed two-local denominator per kernel, cleared before all operations.
"""
from fractions import Fraction
from itertools import product
from math import prod


def add(p, q):
    n = max(len(p), len(q))
    return [(p[i] if i < len(p) else 0) + (q[i] if i < len(q) else 0) for i in range(n)]


def mul(p, q):
    result = [0] * (len(p) + len(q) - 1)
    for i, c in enumerate(p):
        for j, v in enumerate(q):
            result[i+j] += c*v
    return result


def v2(x):
    return (abs(x) & -abs(x)).bit_length()-1


def kernel(L, t, offset):
    poly = [1]
    for s in range(-L, L):
        if s != offset:
            poly = mul(poly, [t-s, 2*L])
    denominator = prod(-s for s in range(-L, L) if s)
    return [Fraction(c, denominator) for c in poly]


def content():
    # Two old edges, each joins a disjunction to its degree-one variable
    # tensor. Ports 0,2 use bit 0; ports 1,3 use bit 1. All four placements
    # of signs and every distinct assignment of the two clause slots tested.
    from itertools import permutations
    cases = 0
    for perm in permutations(range(4)):
        slots = perm[:2]
        bit = {s: i % 2 for i, s in enumerate(perm)}
        for t in range(-4, 4):
            kernels = {(x,y):kernel(4,t,y-x) for x in slots for y in perm}
            b = len({bit[x+t] for x in slots if x+t in bit})
            for signs in product([False,True], repeat=2):
                total = [0]
                for assignment in product([0,1], repeat=2):
                    bad = [1]
                    for x, positive in zip(slots, signs):
                        w = [0]
                        for y in perm:
                            if assignment[bit[y]]:
                                w = add(w,kernels[x,y])
                        bad = mul(bad,add([1],[-a for a in w]) if positive else w)
                    total = add(total,add([1],[-a for a in bad]))
                for k, c in enumerate(map(Fraction,total)):
                    if c:
                        assert v2(c.numerator)-v2(c.denominator)>=max(k,2-b)
                cases += 1
    return cases


def stack(L, n, edges):
    # Direct rational sum over every subdivision bit, with no wrapped-table
    # substitution. At zeta=1 the odd denominators are inverted modulo 2^(U+1).
    m = 2*len(edges)
    U = (L-1)*m
    modulus = 1 << (U+1)
    sample = 1-L+2*L
    base = prod(-s for s in range(-L,L) if s)
    def entry(offset):
        a = Fraction(prod(sample-s for s in range(-L,L) if s != offset),base)
        assert a.denominator % 2
        return a.numerator * pow(a.denominator,-1,modulus) % modulus
    tables = []
    for mask in range(1<<L):
        tables.append([sum(entry(y-x) for y in range(L) if mask>>y&1)%modulus for x in range(L)])
    incident = [[2*i+j for i,e in enumerate(edges) for j,w in enumerate(e) if w==v] for v in range(n)]
    total = 0
    for masks in product(range(1<<L),repeat=m):
        value = 1
        for x in range(L):
            w = [tables[a][x] for a in masks]
            for i in range(0,m,2):
                value = value*(1-(1-w[i])*(1-w[i+1]))%modulus
            for ids in incident:
                if len(ids)>1:
                    value = value*(prod(w[i] for i in ids)+prod(1-w[i] for i in ids))%modulus
        total = (total+value)%modulus
    independent = sum(all(not(mask>>a & mask>>b & 1) for a,b in edges) for mask in range(1<<n))
    assert total == (independent%2)<<U, (edges,total,U,independent)
    return L,edges,U,total,independent


def fillers():
    from itertools import permutations
    L = 4
    t = 1-L
    cases = 0
    for perm in permutations(range(4)):
        # First two ports are clause rows, last two degree-one variable rows.
        # Each bit is shared by the two port slots of the same unit.
        bit = {s:i % 2 for i,s in enumerate(perm)}
        for cuts in [((0,1,2,3),), ((0,1),(2,3)), ((0,3),(1,2)), ((0,),(1,2,3))]:
            packet = {x:part for part in cuts for x in part}
            rows = perm[:2]
            ordinary = {bit[x+t] for x in rows if x+t in packet[x]}
            U = 2-len(ordinary)
            pos = set()
            seen = set()
            for x in rows:
                y = (x+t)%L
                if y in packet[x] and bit[y] not in ordinary and bit[y] not in seen:
                    pos.add(x)
                    seen.add(bit[y])
            total = 0
            for a in product([0,1],repeat=2):
                w = {x:sum(sum(kernel(L,t,y-x))*a[bit[y]] for y in packet[x]) for x in rows}
                total += prod(w[x] if x in pos else 1-w[x] for x in rows)
            assert total and v2(total.numerator)-v2(total.denominator)==U
            cases += 1
    return cases


if __name__ == '__main__':
    print('Direct jet content cases',content(),flush=True)
    print('Direct filler cases',fillers(),flush=True)
    for L,n,edges in [(2,2,[(0,1)]),(2,3,[(0,1),(1,2)]),(2,3,[(0,1),(1,2),(2,0)]),
                      (2,4,[(0,1),(0,2),(0,3)]),(4,2,[(0,1)]),(4,3,[(0,1),(1,2)])]:
        print('Direct stack L, edges, U, residue, independent sets:',stack(L,n,edges),flush=True)
