"""Sparse source 3-CNF compiled into shared NAND pair wires and binary clauses."""
from source_pair_cover import solve_scopes
from itertools import combinations


def compile_source(n,clauses,*,pins=(),pair_node_cap=0):
    if pair_node_cap is not None and (type(pair_node_cap) is not int or pair_node_cap < 0):
        raise ValueError("invalid pair search cap")
    if type(n) is not int or n<0:
        raise ValueError("invalid declared arity")
    original = tuple(tuple(row) for row in clauses)
    if any(len(row)>3 for row in original) or any(type(x) is not int or not 1<=abs(x)<=n for row in original for x in row):
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
                  residual=tuple(sorted(rows)),clauses=(),observed=(),pair_count=0,banks=(),pair_search=None,pair_cover=(),
                  not_gates=0,pair_frequency_visits=0)
    if conflict or () in rows or not rows:
        result["status"] = "UNSAT" if conflict or () in rows else "SAT"
        return result
    active = tuple(sorted({abs(x) for row in rows for x in row}))
    index = {j:i for i,j in enumerate(active)}
    def literal(x):
        return (index[abs(x)]+1)*(1 if x>0 else -1)
    exterior = [tuple(map(literal,row)) for row in sorted(rows) if len(row)<3]
    ternary = sorted(row for row in rows if len(row)==3)
    scopes = {tuple(sorted(map(abs,row))) for row in ternary}
    search = solve_scopes(scopes,node_cap=pair_node_cap)
    cover = set(map(tuple,search["cover"]))
    assigned = {}
    for row in ternary:
        signed = {abs(x):x for x in row}
        pair = next(p for p in combinations(sorted(signed),2) if p in cover)
        terms = tuple(signed[v] for v in pair)
        rest = next(x for x in row if abs(x) not in pair)
        assigned.setdefault(pair,{}).setdefault(terms,[]).append(rest)
    gates = []
    banks = []
    def append_gate(a,b):
        gates.append((a,b))
        return len(active)+len(gates)-1
    for pair,patterns in sorted(assigned.items()):
        start = len(gates)
        negated = {}
        for terms,rests in sorted(patterns.items()):
            inputs = []
            for x in terms:
                wire = index[abs(x)]
                if x>0:
                    if wire not in negated:
                        negated[wire] = append_gate(wire,wire)
                    wire = negated[wire]
                inputs.append(wire)
            output = append_gate(*inputs)+1
            exterior.extend((output,literal(rest)) for rest in rests)
        banks.append((start,len(gates)))
    result.update(status="ok",inputs=len(active),active=active,gates=tuple(gates),
                  clauses=tuple(exterior),observed=tuple(sorted({abs(x)-1 for row in exterior for x in row})),
                  not_gates=sum(a==b for a,b in gates),banks=tuple(banks),pair_search=search,pair_count=len(banks),pair_cover=tuple(sorted(assigned)))
    return result
