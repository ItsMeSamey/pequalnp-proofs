from itertools import product, combinations
from pathlib import Path
from functools import cache
from pysat.card import CardEnc, EncType
from pysat.formula import IDPool
from proof import VerifiedSolver as Solver
import sys, json
ROOT = Path(__file__).parent

def eligible(k, p):
    d = k - p
    options = [[(a, b) for a in range(1 << min(i, d)) for b in range(a, 1 << min(i, d))] for i in range(k)]
    for deps in product(*options):
        live = (1 << p) - 1 << d
        for i in reversed(range(k)):
            if live >> i & 1:
                live |= deps[i][0] | deps[i][1]
        if live != (1 << k) - 1:
            continue
        clauses = set()
        for pat in range(1 << k):
            live = (1 << p) - 1 << d
            cl = 0
            for i in reversed(range(k)):
                if live >> i & 1:
                    b = pat >> i & 1
                    cl |= 1 << 2 * i + b
                    live |= deps[i][b]
            clauses.add(cl)
        cs = []
        for cl in sorted(clauses, key=lambda m: (m.bit_count(), m)):
            if all((old & ~cl for old in cs)):
                cs.append(cl)
        if len(cs) < 12:
            continue
        vals = [evaluate_signature((1 << 2 * k) - 1 ^ cl, deps) for cl in cs]
        if not all((any((st >> i & 1 for st in vals)) for i in range(d))):
            continue
        yield (deps, cs)

def evaluate_signature(mask, deps):
    state = 0
    for i, (a, b) in enumerate(deps):
        if (mask >> 2 * i & 1 or state & a) and (mask >> 2 * i + 1 & 1 or state & b):
            state |= 1 << i
    return state

def fit(deps, clauses, chosen, p, budget):
    k = len(deps)
    n = 2 * k
    d = k - p
    pool = IDPool()
    wire = {m: pool.id() for m in range(1, 1 << n)}
    raw_options = [[m for m in wire if not m & c and all((m & other for other in chosen if other != c))] for c in chosen]
    dirty = [sum((1 << 2 * i + b for i, pair in enumerate(deps) for b, s in enumerate(pair) if s >> j & 1)) for j in range(d)]
    possible = {m for m in wire if any((not m & ~s for choices in raw_options for s in choices)) or any((not m & ~s for s in dirty))}
    with Solver(name='cadical195') as solver:
        for m, v in wire.items():
            if m not in possible:
                solver.add_clause([-v])
                continue
            if m.bit_count() == 1:
                solver.add_clause([v])
                continue
            parts = [x for x in possible if x != m and (not x & ~m)]
            witnesses = []
            for a, b in combinations(parts, 2):
                if a | b != m:
                    continue
                w = pool.id()
                witnesses.append(w)
                solver.add_clause([-w, wire[a]])
                solver.add_clause([-w, wire[b]])
            solver.add_clause([-v] + witnesses)
        for m in dirty:
            solver.add_clause([wire[m]])
        solver.append_formula(CardEnc.atmost([wire[m] for m in possible if m.bit_count() > 1], budget, vpool=pool, encoding=EncType.seqcounter).clauses)
        selectors = []
        for opts in raw_options * 2:
            sel = {m: pool.id() for m in opts}
            solver.add_clause(list(sel.values()))
            for m, s in sel.items():
                solver.add_clause([-s, wire[m]])
            selectors.append(sel)
        for extra in set(clauses) - set(chosen):
            miss = []
            for sel in selectors:
                z = pool.id()
                miss.append(z)
                for m, s in sel.items():
                    if not m & extra:
                        solver.add_clause([-s, z])
            for i in range(12):
                for j in range(12):
                    if i != j:
                        solver.add_clause([-miss[i], -miss[12 + j]])
        ok = solver.solve_checked()
        if ok is not True:
            return (ok, None)
        mod = set(solver.get_model())
        raw = [next((m for m, s in sel.items() if s in mod)) for sel in selectors]
        library = sorted([m for m, v in wire.items() if v in mod], key=lambda m: (m.bit_count(), m))
        return (True, {'deps': deps, 'raw': raw, 'library': library, 'dirty': dirty, 'p': p})
