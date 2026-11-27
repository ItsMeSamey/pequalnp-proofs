"""Parsimonious signed-DIMACS clause lift to a zero target over GF(2).

Complete forbidden parity classes on one variable support yield affine rows.
The other clauses use products of literal falsity bits. Each intermediate bit
has exactly one allowed value. Original variables occupy the low n bits.
"""
from dataclasses import dataclass
from quadratic_image import Quadratic


@dataclass(frozen=True)
class Lift:
    variables: int
    forms: tuple
    equations: tuple
    parity_blocks: int


def lift(n, clauses, equations=()):
    """Return forms required to vanish and affine (mask, RHS) equations."""
    if type(n) is not int or n < 0:
        raise ValueError("invalid variable count")
    rows = list(equations)
    if any(type(a) is not int or a < 0 or a.bit_length() > n or b not in (0,1)
           for a,b in rows):
        raise ValueError("invalid affine row")
    groups = {}
    for clause in clauses:
        lits = set(clause)
        if any(type(k) is not int or not 1 <= abs(k) <= n for k in lits):
            raise ValueError("invalid literal")
        if any(-k in lits for k in lits):
            continue
        if not lits:
            rows.append((0,1))
            continue
        scope = tuple(sorted(abs(k)-1 for k in lits))
        forbidden = sum(1 << j for j,i in enumerate(scope) if -(i+1) in lits)
        groups.setdefault(scope,set()).add(forbidden)

    forms = []
    next_id = n
    blocks = 0
    for scope, forbidden in groups.items():
        for parity in (0,1):
            patterns = sorted(p for p in forbidden if p.bit_count() % 2 == parity)
            if len(patterns) == 1 << (len(scope)-1):
                rows.append((sum(1 << i for i in scope),1-parity))
                blocks += 1
                continue
            for pattern in patterns:
                # Factor x_i+c is 1 exactly at the forbidden value for bit i.
                i = scope[0]
                c = 1 ^ (pattern & 1)
                for j,v in enumerate(scope[1:],1):
                    d = 1 ^ ((pattern >> j) & 1)
                    linear = (d << i) ^ (c << v)
                    last = j == len(scope)-1
                    if not last:
                        linear ^= 1 << next_id
                    forms.append(Quadratic(c & d,linear,((i,v),)))
                    if not last:
                        i, c = next_id, 0
                        next_id += 1
    return Lift(next_id,tuple(forms),tuple(rows),blocks)


def solve_cnf(n, clauses, equations=(), *, max_phase_evals=65536, max_field_size=None):
    """Return (status, count, packed original witness).

    SAT may have an unknown count. Exhausted probes return UNKNOWN unless an
    optional capped full-image enumeration settles the target. Set the probe
    budget to zero to request only preprocessing and optional enumeration.
    """
    from quadratic_target import prepare
    from quadratic_probe import probe
    from quadratic_image import discover, FieldBudgetExceeded
    if type(max_phase_evals) is not int or max_phase_evals < 0:
        raise ValueError("invalid phase budget")
    if max_field_size is not None and (type(max_field_size) is not int or max_field_size < 2):
        raise ValueError("invalid field budget")
    clauses = tuple(tuple(c) for c in clauses)
    equations = tuple(equations)
    instance = lift(n,clauses,equations)
    red = prepare(instance.variables,instance.forms,0,instance.equations)
    if red is None:
        return "UNSAT",0,None
    if not red.forms:
        count, u = 1 << red.n, 0
    else:
        result = probe(red.n,red.forms,red.target,max_phase_evals=max_phase_evals)
        if result.status == "UNSAT":
            return "UNSAT",0,None
        count, u = result.count, result.witness
        if result.status == "UNKNOWN":
            if max_field_size is None:
                return "UNKNOWN",None,None
            try:
                image = discover(red.n,red.forms,max_field_size=max_field_size)
            except FieldBudgetExceeded:
                return "UNKNOWN",None,None
            if red.target not in image:
                return "UNSAT",0,None
            count,u = image[red.target]
    x = red.lift(u) & ((1 << n)-1)
    if not (all(any(((x >> (abs(k)-1)) & 1) == (k>0) for k in c) for c in clauses)
            and all((a & x).bit_count() % 2 == b for a,b in equations)):
        raise ArithmeticError("projected witness fails original constraints")
    return "SAT",None if count is None else count*red.multiplicity,x


def self_test():
    from quadratic_image import evaluate
    from itertools import product
    from random import Random
    rng = Random(314)
    for _ in range(80):
        n = rng.randint(1,4)
        clauses = [[rng.choice((-1,1))*i for i in rng.sample(range(1,n+1),rng.randrange(n+1))]
                   for _ in range(rng.randrange(4))]
        instance = lift(n,clauses)
        counts = [0]*(1<<n)
        for x in range(1 << instance.variables):
            if (all((x&a).bit_count()%2 == b for a,b in instance.equations)
                    and evaluate(instance.forms,x) == 0):
                counts[x % (1<<n)] += 1
        truth = [all(any(((x>>(abs(k)-1))&1)==(k>0) for k in c) for c in clauses)
                 for x in range(1<<n)]
        assert counts == truth
        status,count,w = solve_cnf(n,clauses)
        assert status == ("SAT" if any(truth) else "UNSAT")
        assert count is None or count == sum(truth)
        assert w is None or truth[w]
    def forbid(scope, rhs):
        return [tuple(-i if a else i for i,a in zip(scope,bits))
                for bits in product((0,1),repeat=len(scope)) if sum(bits)%2 != rhs]
    # K4 is cubic; each edge variable occurs at its two incident vertices.
    blocks = [forbid(scope,0) for scope in [(1,2,3),(1,4,5),(2,4,6),(3,5,6)]]
    even = sum(blocks,[])
    assert lift(6,even).parity_blocks == 4
    assert solve_cnf(6,even,max_phase_evals=0) == ("SAT",8,0)
    odd = sum(blocks[:3],[]) + forbid((3,5,6),1)
    assert solve_cnf(6,odd,max_phase_evals=0) == ("UNSAT",0,None)
    assert lift(6,odd[:-1]).parity_blocks == 3
    assert solve_cnf(6,odd[:-1])[0] == "SAT"
    assert solve_cnf(4,[],[(3,1)])[1] == 8
    assert solve_cnf(2,[(1,2)],max_phase_evals=0) == ("UNKNOWN",None,None)
    assert solve_cnf(2,[(1,2)],max_phase_evals=0,max_field_size=64)[1] == 3
    assert solve_cnf(4,[(1,2),(3,4)],max_phase_evals=0,max_field_size=2)[0] == "UNKNOWN"
    assert solve_cnf(0,[()]) == ("UNSAT",0,None)


if __name__ == "__main__":
    self_test()
    print("CNF lift and solver checks passed")
