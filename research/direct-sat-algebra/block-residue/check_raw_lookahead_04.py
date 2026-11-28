"""Independent raw cofactor cost and original NAND witness oracles."""
from itertools import product
from random import Random
from check_pair_gain_04 import cost_oracle
from check_distinct_cones_04 import partitions
from raw_lookahead import solve


def cost(n, gates, rows, fixed):
    aliases = [(None, fixed[v]) if v in fixed else (v,0) for v in range(n)]
    retained = []
    for a,b in gates:
        ops = aliases[a], aliases[b]
        names = sorted({v for v,s in ops if v is not None})
        table = []
        for bits in product(range(2), repeat=len(names)):
            vals = dict(zip(names,bits))
            vals[None] = 0
            table.append(int(not all(vals[v]^s for v,s in ops)))
        if min(table) == max(table):
            aliases.append((None,table[0]))
        elif len(names) == 1:
            aliases.append((names[0],table[0]))
        else:
            aliases.append((n+len(retained),0))
            retained.append(ops)
    material, pieces, wires = [], [], list(range(n))
    for ops in retained:
        start = len(material)
        new = []
        for v,s in ops:
            w = wires[v]
            if s:
                material.append((w,w))
                w = n+len(material)-1
            new.append(w)
        material.append(tuple(new))
        wires.append(n+len(material)-1)
        pieces.append(tuple(range(start,len(material))))
    observed = set()
    for row in rows:
        lits = {(aliases[abs(l)-1][0],aliases[abs(l)-1][1]^(l<0)) for l in row}
        if (None,1) in lits or any((v,s^1) in lits for v,s in lits):
            continue
        observed.update(wires[v] for v,s in lits if v is not None)
    score = cost_oracle(n,material,observed)
    best = len(retained)+1
    for family in partitions(len(retained)):
        vals = [score(tuple(sorted(i for j in g for i in pieces[j]))) for g in family]
        if None not in vals:
            best = min(best,sum(vals))
    return best


def check(n,gates,clauses=(),pins=(),equalities=(),output=None):
    rows = list(clauses)
    for v,k in list(pins)+([(output,1)] if output is not None else []):
        rows.append(((v+1) if k else -(v+1),))
    for u,v,s in equalities:
        a,b = u+1,(v+1)*(-1 if s else 1)
        rows.extend(((-a,b),(a,-b)))
    baseline = cost(n,gates,rows,{})
    best = 1 << baseline
    selected, children = None,(baseline,)
    for v in range(n):
        bad = tuple(cost(n,gates,rows,{v:k}) for k in range(2))
        price = sum(1 << k for k in bad)
        if price < best:
            selected, children, best = v,bad,price
    state, base, chosen, scores, raw = solve(n,gates,clauses=clauses,pins=pins,
                                              equalities=equalities,output=output)
    assert (base,chosen,tuple(scores)) == (baseline,selected,children)
    def accepts(word):
        w = list(word)
        for a,b in gates:
            w.append(int(not (w[a] and w[b])))
        return all(any(w[abs(l)-1] == (l>0) for l in row) for row in rows)
    feasible = any(accepts(word) for word in product(range(2),repeat=n))
    assert state == ('sat' if feasible else 'unsat')
    if feasible:
        assert len(raw)==n and all(v in (0,1) for v in raw) and accepts(raw)
    else:
        assert raw is None
    return chosen


def main():
    check(0,[])
    check(0,[],clauses=[()])
    check(2,[],clauses=[(-1,)],output=0)
    gates = [(0,i) for i in range(1,5)]
    for k in (0,1):
        assert check(5,gates,pins=[(i,k) for i in range(1,5)]+[(i,1) for i in range(5,9)],
                     output=0) == 0
    assert check(2,[(0,1)],pins=[(0,1),(1,1)],output=2) is None
    rng = Random(91123)
    for case in range(65):
        n = rng.randrange(1,5)
        gates = [(rng.randrange(n+i),rng.randrange(n+i)) for i in range(case%6)]
        total = n+len(gates)
        pins = [(rng.randrange(total),rng.randrange(2))]
        eqs = [(rng.randrange(total),rng.randrange(total),rng.randrange(2))]
        rows = [tuple(rng.choice((-1,1))*rng.randrange(1,total+1) for _ in range(case%3))]
        check(n,gates,rows,pins,eqs,rng.randrange(total))
    print("71 raw lookahead cases, every raw cofactor and signed gate partition")


if __name__ == '__main__':
    main()
