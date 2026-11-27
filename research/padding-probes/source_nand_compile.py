"""Compile sparse DIMACS literals to a zero-based ordinary NAND circuit."""
from interval_optimizer import interval_witness


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
        if any(-x in literals or (abs(x) in fixed and fixed[abs(x)]==(x>0)) for x in literals):
            continue
        rows.add(tuple(sorted(x for x in literals if abs(x) not in fixed)))
    result = dict(n=n,original=original,fixed=fixed,inputs=0,gates=(),target=None,active=(),
                  residual=tuple(sorted(rows)),not_gates=0,other_gates=0)
    if conflict or () in rows or not rows:
        result["status"] = "UNSAT" if conflict or () in rows else "SAT"
        return result
    active = tuple(sorted({abs(x) for row in rows for x in row}))
    index = {j:i for i,j in enumerate(active)}
    gates = []
    opposite = {}
    def nand(a,b):
        gates.append((a,b))
        return len(active)+len(gates)-1
    def negate(a):
        if a not in opposite:
            b = nand(a,a)
            opposite[a] = b
            opposite[b] = a
            result["not_gates"] += 1
        return opposite[a]
    clause_wires = []
    for row in result["residual"]:
        terms = [index[abs(x)] if x>0 else negate(index[-x]) for x in row]
        wire = terms[0]
        for term in terms[1:]:
            wire = nand(negate(wire),negate(term))
        clause_wires.append(wire)
    wire = clause_wires[0]
    for term in clause_wires[1:]:
        wire = negate(nand(wire,term))
    result.update(status="ok",inputs=len(active),active=active,gates=tuple(gates),target=wire,
                  other_gates=len(gates)-result["not_gates"])
    return result


def lift(compiled,raw):
    raw = tuple(raw)
    if (compiled["status"]=="UNSAT" or len(raw)!=compiled["inputs"] or
            any(type(b) not in (int,bool) or b not in (0,1) for b in raw)):
        raise ValueError("invalid input witness")
    wires = list(raw)
    for a,b in compiled["gates"]:
        wires.append(1^(wires[a]&wires[b]))
    if compiled["target"] is not None and wires[compiled["target"]]!=1:
        raise ValueError("output pin failed")
    true = {j for j,b in compiled["fixed"].items() if b}
    true.update(j for j,b in zip(compiled["active"],raw) if b)
    if any(not any((abs(x) in true)==(x>0) for x in row) for row in compiled["original"]):
        raise ValueError("original clauses failed")
    return tuple(sorted(true))


def solve_source(n,clauses,*,pins=()):
    compiled = compile_source(n,clauses,pins=pins)
    if compiled["status"]!="ok":
        sat = compiled["status"]=="SAT"
        return dict(status=compiled["status"],witness=lift(compiled,()) if sat else None,
                    bad_blocks=0,intervals=())
    b,intervals,raw = interval_witness(compiled["inputs"],compiled["gates"],
                                       pins=((compiled["target"],1),))
    return dict(status="UNSAT" if raw is None else "SAT",
                witness=None if raw is None else lift(compiled,raw),bad_blocks=b,intervals=intervals)
