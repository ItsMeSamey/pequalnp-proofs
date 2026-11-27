"""Exact quadratic target counts by splitting radical cosets and Gauss phases.

Input uses isotropic_target.count's packed squarefree vector ANF. At a prefix
of the greedy radical chain let a be the removed dimension and p the rank of
the remaining quadratic coefficient vectors (equivalently the polar span).
The algorithm chooses a prefix minimizing a+p, including both endpoints.
It uses 2^(a+p) poly(input length) bit operations and polynomial working space.
The cap controls that exponent; exhaustion returns no count or witness.
"""
from quadratic_image import bits, gauss, parity
from quadratic_target import (affine_domain, apply_basis, evaluate_anf, insert,
                              interpolate, reduce_vector)


def choose_split(n, pairs):
    basis = [1 << i for i in range(n)]
    complement = []
    best_cost = None
    while True:
        def restricted(x):
            return evaluate_anf(0, [0]*n, pairs, apply_basis(basis,x))
        polar = interpolate(restricted,len(basis))[2]
        span = {}
        for coefficient in polar.values():
            insert(coefficient,0,span)
        cost = len(complement) + len(span)
        if best_cost is None or cost < best_cost:
            best_cost = cost
            best = tuple(complement),tuple(basis),span
        if not span:
            return best
        entry = next(iter(polar.values()))
        bit = entry & -entry
        rows = [0]*len(basis)
        for (i,j), value in polar.items():
            if value & bit:
                rows[i] |= 1 << j
                rows[j] |= 1 << i
        _,kernel,pivots = affine_domain(len(basis),((row,0) for row in rows))
        complement.extend(basis[i] for i in pivots)
        basis = [apply_basis(basis,v) for v in kernel]


def count(n, constant, linear, pairs, target, cap=None, *, split_provider=choose_split):
    """Return (exact count, one packed witness, selected exponent)."""
    complement, flat, span = split_provider(n,pairs)
    cost = len(complement)+len(span)
    if cap is not None and cost > cap:
        return None,None,cost
    pivots = sorted(span)
    def value(x):
        return evaluate_anf(constant,linear,pairs,x) ^ target
    total = 0
    witness = None
    for mask in range(1 << len(complement)):
        origin = apply_basis(complement,mask)
        def remainder_at(v):
            return reduce_vector(value(origin ^ v),span)[0]
        # Modulo the polar span the whole output is affine on this coset.
        base = remainder_at(0)
        cols = [remainder_at(v)^base for v in flat]
        active = base
        for col in cols:
            active |= col
        equations = [(sum(((col>>j)&1)<<i for i,col in enumerate(cols)),(base>>j)&1)
                     for j in bits(active)]
        chart = affine_domain(len(flat),equations)
        if chart is None:
            continue
        offset,kernel,_ = chart
        seed = origin ^ apply_basis(flat,offset)
        directions = [apply_basis(flat,v) for v in kernel]
        def output(x):
            residual = value(seed ^ apply_basis(directions,x))
            # The pivot coordinates distinguish all elements of span.
            return sum(((residual>>j)&1)<<i for i,j in enumerate(pivots))
        c, lin, quad = interpolate(output,len(kernel))
        def mass(fixed, assignment):
            result = 0
            for character in range(1 << len(span)):
                form = (parity(character & c),
                        sum(parity(character & v)<<i for i,v in enumerate(lin)),
                        frozenset(pair for pair,v in quad.items() if parity(character & v)))
                result += gauss(len(kernel),form,fixed,assignment)
            return result // (1 << len(span))
        hits = mass(0,0)
        total += hits
        if hits and witness is None:
            fixed = assignment = 0
            for i in range(len(kernel)):
                fixed |= 1 << i
                if mass(fixed,assignment) == 0:
                    assignment |= 1 << i
            witness = seed ^ apply_basis(directions,assignment)
            if value(witness):
                raise ArithmeticError("hybrid witness fails target")
    return total,witness,cost


def self_test():
    from itertools import combinations
    from random import Random
    rng = Random(341)
    for n in range(7):
        for _ in range(12):
            p = rng.randrange(5)
            pairs = {edge:rng.randrange(1<<p) for edge in combinations(range(n),2)}
            linear = [rng.randrange(1<<p) for _ in range(n)]
            c = rng.randrange(1<<p)
            vals = [evaluate_anf(c,linear,pairs,x) for x in range(1<<n)]
            for target in range(1<<p):
                hits,w,_ = count(n,c,linear,pairs,target)
                assert hits == vals.count(target)
                assert w is None if hits == 0 else vals[w] == target
    # Four spokes sharing a hub, plus one disjoint rank-four symplectic form.
    # Prefix exponents are respectively 0+5, 2+1 and 6+0.
    pairs = {(0,i):1<<(i-1) for i in range(1,5)}
    pairs.update({(5,6):16,(7,8):16})
    comp,flat,span = choose_split(9,pairs)
    assert (len(comp),len(span)) == (2,1)
    for target in range(32):
        hits,w,cost = count(9,0,[0]*9,pairs,target)
        vals = [evaluate_anf(0,[0]*9,pairs,x) for x in range(512)]
        assert cost == 3 and hits == vals.count(target) and vals[w] == target
    assert count(9,0,[0]*9,pairs,0,cap=2) == (None,None,3)


if __name__ == "__main__":
    self_test()
    print("hybrid counts, witnesses, cap and mixed split verified")
