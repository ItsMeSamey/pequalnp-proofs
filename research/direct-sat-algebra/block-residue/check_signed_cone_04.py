"""Physical raw-word and unrestricted partition oracles for signed aliases."""
from itertools import product
from random import Random
from check_pair_gain_04 import cost_oracle
from check_distinct_cones_04 import partitions
from signed_cone_nand import solve, normalize


def check(n, gates, pins=(), clauses=(), equalities=(), output=None):
    retained, aliases = normalize(n, gates)
    def read(ref, vals):
        base, flip = ref
        assert -1 <= base < len(vals) and flip in (0, 1)
        return flip if base == -1 else vals[base] ^ flip
    def physical(raw):
        w = list(raw)
        for a, b in gates:
            w.append(int(not (w[a] and w[b])))
        return w
    def accepts(w):
        return ((output is None or w[output]) and all(w[v] == k for v,k in pins)
                and all(w[x] ^ w[y] == k for x,y,k in equalities)
                and all(any(w[abs(l)-1] == (l > 0) for l in row) for row in clauses))
    exists = False
    for raw in product(range(2), repeat=n):
        vals = list(raw)
        for a, b in retained:
            assert a[0] != b[0]
            vals.append(int(not (read(a, vals) and read(b, vals))))
        w = physical(raw)
        assert [read(ref, vals) for ref in aliases] == w
        exists |= bool(accepts(w))
    observed = {abs(l)-1 for row in clauses for l in row}
    observed.update(v for v,k in pins)
    observed.update(v for x,y,k in equalities for v in (x,y))
    if output is not None:
        observed.add(output)
    score = cost_oracle(n, gates, observed)
    opt = len(gates)+1
    for family in partitions(len(gates)):
        costs = [score(block) for block in family]
        if None not in costs:
            opt = min(opt, sum(costs))
    state, cost, groups, raw = solve(n, gates, pins=pins, equalities=equalities,
                                      clauses=clauses, output=output)
    assert 0 <= cost <= opt, (n, gates, observed, cost, opt)
    assert sorted(i for group in groups for i in group) == list(range(len(retained)))
    assert state == ('sat' if exists else 'unsat')
    if exists:
        assert len(raw) == n and all(b in (0,1) for b in raw) and accepts(physical(raw))
    else:
        assert raw is None
    return cost, opt


def main():
    check(0, [])
    check(0, [], clauses=[()])
    check(2, [], output=0, clauses=[(-1,)])
    gates = [(0,0), (0,2), (3,3), (3,1), (5,2), (4,6)]
    for out in range(8):
        for sign in (-1,1):
            check(2, gates, output=out, clauses=[(sign*4,-6), (-8,7)], equalities=[(0,2,1)])
    for bit in (0,1):
        check(2, gates, pins=[(4,bit)], clauses=[(6,2), (4,-4)])
    assert check(2, [(0,1)], clauses=[(-1,1), (-2,2)], output=2) == (0,1)
    rng = Random(342169)
    for case in range(105):
        n = rng.randrange(1,5)
        gates = []
        for i in range(case % 7):
            a = rng.randrange(n+i)
            gates.append((a, a if rng.randrange(3) == 0 else rng.randrange(n+i)))
        wires = n+len(gates)
        clauses = [tuple(rng.choice((-1,1))*rng.randrange(1,wires+1)
                         for _ in range(rng.choice((1,2,2))))]
        eq = [(rng.randrange(wires),rng.randrange(wires),rng.randrange(2))]
        pins = [(rng.randrange(wires),rng.randrange(2))] if case % 2 else []
        check(n, gates, pins, clauses, eq, rng.randrange(wires))
    print('127 original signed-normalization cases, raw-word and partition oracles')


if __name__ == '__main__':
    main()
