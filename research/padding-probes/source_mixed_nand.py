"""Sparse source 3-CNF compiled into shared NAND pair wires and binary clauses."""
from collections import Counter
from itertools import combinations
from interval_optimizer import interval_witness
from source_nand_compile import lift


def compile_source(n,clauses,*,pins=()):
    if type(n) is not int or n<0:
        raise ValueError("invalid declared arity")
    original = tuple(tuple(row) for row in clauses)
    if any(type(x) is not int or not 1<=abs(x)<=n for row in original for x in row):
        raise ValueError("literal outside declared range")
    fixed = {}
    conflict = False
    for j,bit in pins.items() if hasattr(pins,"items") else pins:
        if type(j) is not int or not 1<=j<=n or type(bit) not in (bool,int) or bit not in (0,1):
            raise ValueError("invalid pin")
        conflict |= j in fixed and fixed[j]!=bit
        fixed[j] = int(bit)
    rows = set()
    for row in original:
        literals = set(row)
        if any(-x in literals or fixed.get(abs(x))==int(x>0) for x in literals):
            continue
        live = tuple(sorted(x for x in literals if abs(x) not in fixed))
        if len(live)>3:
            raise ValueError("residual clause width exceeds three")
        rows.add(live)
    result = dict(n=n,original=original,fixed=fixed,inputs=0,gates=(),target=None,active=(),
                  residual=tuple(sorted(rows)),clauses=(),observed=(),pair_count=0,pair_cover=(),
                  not_gates=0,pair_frequency_visits=0)
    if conflict or () in rows or not rows:
        result["status"] = "UNSAT" if conflict or () in rows else "SAT"
        return result
    active = tuple(sorted({abs(x) for row in rows for x in row}))
    index = {j:i for i,j in enumerate(active)}
    def literal(x):
        return (index[abs(x)]+1)*(1 if x>0 else -1)
    gates = []
    negatives = {}
    def complement(x):
        wire = index[abs(x)]
        if x<0:
            return wire
        if wire not in negatives:
            negatives[wire] = len(active)+len(gates)
            gates.append((wire,wire))
        return negatives[wire]

    exterior = [tuple(map(literal,row)) for row in sorted(rows) if len(row)<3]
    remaining = [row for row in sorted(rows) if len(row)==3]
    selected = []
    while remaining:
        counts = Counter(pair for row in remaining for pair in combinations(row,2))
        result["pair_frequency_visits"] += 3*len(remaining)
        pair = min(counts,key=lambda p:(-counts[p],p))
        a,b = pair
        left,right = complement(a),complement(b)
        pair_wire = len(active)+len(gates)
        gates.append((left,right))
        uncovered = []
        for row in remaining:
            if a in row and b in row:
                other = next(x for x in row if x not in pair)
                exterior.append((pair_wire+1,literal(other)))
            else:
                uncovered.append(row)
        selected.append(pair)
        remaining = uncovered
    observed = tuple(sorted({abs(x)-1 for row in exterior for x in row}))
    result.update(status="ok",inputs=len(active),active=active,gates=tuple(gates),
                  clauses=tuple(exterior),observed=observed,pair_count=len(selected),
                  pair_cover=tuple(selected),not_gates=len(negatives))
    return result


def solve_source(n,clauses,*,pins=()):
    job = compile_source(n,clauses,pins=pins)
    if job["status"]!="ok":
        return dict(status=job["status"],witness=lift(job,()) if job["status"]=="SAT" else None,
                    bad_blocks=0,intervals=(),pair_count=0)
    bad,intervals,raw = interval_witness(job["inputs"],job["gates"],clauses=job["clauses"])
    if bad>job["pair_count"]:
        raise ArithmeticError("singleton partition bound failed")
    return dict(status="UNSAT" if raw is None else "SAT",
                witness=None if raw is None else lift(job,raw),bad_blocks=bad,
                intervals=intervals,pair_count=job["pair_count"])
