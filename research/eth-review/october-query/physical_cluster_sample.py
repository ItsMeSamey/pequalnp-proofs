"""Exact cyclotomic sufficient test for a supplied native physical packet partition."""
from fractions import Fraction
from itertools import product
from math import prod
from sympy import QQ


def bound(z):
    return sum((Fraction(int(q.numerator), int(q.denominator)).__abs__()
                for q in z.to_list()), Fraction())


def certify(clauses, packets, blocks, N, j, baselines=None):
    """Slot is None or (occurrence number, side): 0 clause, 1 variable.
    Blocks partition keys ('c', clause index) and ('v', variable name).
    Unused declared input variables, if any, require their free scalar separately.
    Returns exact algebraic tables and conservative norm certificate, or UNKNOWN.
    """
    F = QQ.cyclotomic_field(N)
    t = F.one + 2 * F.unit ** (j % N)
    occ = [(i, x) for i, row in enumerate(clauses) for x in row]
    h = len(occ)
    assert all(clauses) and packets
    L = len(packets[0])
    assert all(len(p) == L for p in packets)
    assert sorted(v for p in packets for v in p if v is not None) == [
        (i, s) for i in range(h) for s in range(2)]
    den = prod(-s for s in range(-L, L) if s)
    W = {d: prod((t - F(s) for s in range(-L, L) if s != d), start=F.one)/F(den)
         for d in range(1-L,L)}
    rows = {}
    for p in packets:
        for i, port in enumerate(p):
            if port is None:
                continue
            e, side = port
            c, lit = occ[e]
            key = ('c', c) if not side else ('v', abs(lit))
            terms = [(other[0], W[y-i]) for y, other in enumerate(p)
                     if other is not None and W[y-i]]
            rows.setdefault(key, []).append((lit, terms))
    assert sorted(key for B in blocks for key in B) == sorted(rows)
    scopes = [{e for key in B for _, ts in rows[key] for e, _ in ts} for B in blocks]
    scopes2, tables = [], []
    for i,B in enumerate(blocks):
        shared = scopes[i] & set().union(*(s for k,s in enumerate(scopes) if k!=i))
        external = sorted(shared)
        private = sorted(scopes[i] - shared)
        tab = {}
        for bits in product(range(2), repeat=len(external)):
            total = F.zero
            for hidden in product(range(2), repeat=len(private)):
                word = dict(zip(external + private, bits + hidden))
                val = F.one
                for key in B:
                    vs = [(lit, sum((coef for e,coef in ts if word[e]), F.zero))
                          for lit,ts in rows[key]]
                    if key[0] == 'c':
                        val *= F.one-prod((F.one-z if lit>0 else z for lit,z in vs),start=F.one)
                    else:
                        val *= prod((F.one-z for _,z in vs),start=F.one)+prod((z for _,z in vs),start=F.one)
                total += val
            tab[bits] = total / F(2**len(private))
        if all(v == F.zero for v in tab.values()):
            return 'EXACT_ZERO', F.zero
        tables.append(tab)
        scopes2.append(shared)
    C = F(2**h)
    active = []
    for i,tab in enumerate(tables):
        vals = list(tab.values())
        if all(v==vals[0] for v in vals):
            C *= vals[0]
            continue
        c = baselines[i] if baselines is not None else sum(vals,F.zero)/F(len(vals))
        if not c:
            return 'UNKNOWN', None
        C *= c
        active.append((scopes2[i], {x:v/c-F.one for x,v in tab.items()}))
    if not active:
        return 'EXACT', C
    D=max(1,max(sum(bool(s&t) for t,_ in active)-1 for s,_ in active))
    eta=Fraction(1,100*(D+1))
    if any(bound(v)>eta for _,t in active for v in t.values()):
        return 'UNKNOWN', None
    U=bound(C)*(1+eta)**len(active)
    return 'CERTIFIED', (C,U,active)
