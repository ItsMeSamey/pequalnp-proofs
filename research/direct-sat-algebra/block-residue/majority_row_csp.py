"""Complete optional multisorted majority chart for tiny row domains."""
from itertools import combinations, permutations, product

from corridor_nand import _net, _replay, _rows, _sat
from promoted_row_csp import _promote
from row_csp import _prepare, _relations


def _validate(domains, relations):
    domains = [tuple(domain) for domain in domains]
    if len(relations) != len(domains):
        raise ValueError("wrong adjacency length")
    for domain in domains:
        if (len(domain)>4 or len(set(domain))!=len(domain)
                or any(type(v) is not int or v<0 for v in domain)):
            raise ValueError("invalid row domain")
    for i, adj in enumerate(relations):
        for j, rel in adj.items():
            if type(j) is not int or not 0<=j<len(domains) or i==j:
                raise ValueError("invalid edge")
            if any(a not in domains[i] or b not in domains[j] for a,b in rel):
                raise ValueError("invalid relation")
            if relations[j].get(i) != {(b,a) for a,b in rel}:
                raise ValueError("asymmetric relation")
    return domains


def _pc(domains, constraints):
    """Strong path consistency followed by deterministic greedy extension."""
    D = [set(domain) for domain in domains]
    n = len(D)
    pairs = {}
    def store(i,j,allowed):
        pairs[i,j] = allowed
        pairs[j,i] = {(b,a) for a,b in allowed}
    for i,j in combinations(range(n),2):
        allowed = set(product(D[i],D[j]))
        if (i,j) in constraints:
            allowed.intersection_update(constraints[i,j])
        store(i,j,allowed)
    changed = True
    while changed:
        changed = False
        for i in range(n):
            for j in range(n):
                if i!=j:
                    keep = {a for a,b in pairs[i,j] if b in D[j]}
                    if not D[i].issubset(keep):
                        D[i].intersection_update(keep)
                        changed = True
            if not D[i]:
                return None
        for i,j in combinations(range(n),2):
            prior = pairs[i,j]
            keep = {(a,b) for a,b in prior if a in D[i] and b in D[j]
                    and all(any((a,c) in pairs[i,k] and (b,c) in pairs[j,k] for c in D[k])
                            for k in range(n) if k!=i and k!=j)}
            if not keep:
                return None
            if len(keep)<len(prior):
                store(i,j,keep)
                changed = True
    result = {}
    for i in range(n):
        for a in sorted(D[i]):
            if all((b,a) in pairs[j,i] for j,b in result.items()):
                result[i]=a
                break
        else:
            return None
    return result


def _forced(t):
    a,b,c=t
    if a==b or a==c:
        return a
    if b==c:
        return b
    return None


def majority_assignment(domains, relations, *, max_pc_vars=96):
    """Return status, validated operation tables, and original row choices.

    A capacity skip, absence of a majority, and CSP unsatisfiability have
    distinct outcomes. Row labels can be sparse; each sort has size at most four.
    """
    domains = _validate(domains,relations)
    if max_pc_vars is not None and (type(max_pc_vars) is not int or max_pc_vars<0):
        raise ValueError("invalid PC variable cap")
    if any(not d for d in domains) or any(not r for adj in relations for r in adj.values()):
        return "unsat", None, None
    count = sum(len(d)*(len(d)-1)*(len(d)-2) for d in domains)
    if max_pc_vars is not None and max(len(domains),count)>max_pc_vars:
        return "cap", None, None
    ids = {}
    choices = []
    for i,domain in enumerate(domains):
        for triple in permutations(domain,3):
            ids[i,triple]=len(choices)
            choices.append(set(domain))
    edges={(i,j):set(rel) for i,adj in enumerate(relations) for j,rel in adj.items() if i<j}
    restrictions={}
    for (i,j),rel in edges.items():
        for triple in product(rel,repeat=3):
            left,right=map(tuple,zip(*triple))
            a,b=_forced(left),_forced(right)
            if a is None and b is None:
                key=ids[i,left],ids[j,right]
                if key in restrictions:
                    restrictions[key].intersection_update(rel)
                else:
                    restrictions[key]=set(rel)
            elif a is None:
                choices[ids[i,left]].intersection_update(x for x,y in rel if y==b)
            elif b is None:
                choices[ids[j,right]].intersection_update(y for x,y in rel if x==a)
            elif (a,b) not in rel:
                return "skip", None, None
    values = _pc(choices,restrictions)
    if values is None:
        return "skip", None, None
    tables=[]
    for i,domain in enumerate(domains):
        table={}
        for t in product(domain,repeat=3):
            value=_forced(t)
            table[t]=values[ids[i,t]] if value is None else value
            if table[t] not in domain or (value is not None and table[t]!=value):
                raise AssertionError("invalid majority operation")
        tables.append(table)
    for (i,j),rel in edges.items():
        for triple in product(rel,repeat=3):
            left,right=map(tuple,zip(*triple))
            if (tables[i][left],tables[j][right]) not in rel:
                raise AssertionError("majority certificate failed preservation")
    chosen = _pc(domains,edges)
    if chosen is None:
        return "unsat", tables, None
    if any((chosen[i],chosen[j]) not in rel for (i,j),rel in edges.items()):
        raise AssertionError("row model violates input relation")
    return "sat", tables, chosen


def solve(inputs, gates, *, clauses=(), pins=(), equalities=(), output=None, max_pc_vars=96):
    """Solve on promoted physical rows; replay every NAND wire and original row."""
    gates = _net(inputs,gates)
    if max_pc_vars is not None and (type(max_pc_vars) is not int or max_pc_vars<0):
        raise ValueError("invalid PC variable cap")
    if output is not None:
        if type(output) is not int or not 0<=output<inputs+len(gates):
            raise ValueError("invalid designated output")
        pins=tuple(pins)+((output,1),)
    original=_rows(inputs+len(gates),clauses,pins,equalities)
    physical,expanded,aliases,base,factors,tables=_prepare(inputs,gates,original)
    n=inputs+len(physical)
    stats=dict(initial_bad=len(tables),bad=len(tables),promoted=0,pruned=0)
    rows=_promote(n,base,tables,stats)
    if rows is None:
        return "unsat",stats,None
    if max_pc_vars is not None and len(rows)>max_pc_vars:
        stats["reason"]="cap"
        return "skip",stats,None
    pairwise=_relations(n,base,rows)
    if pairwise is None:
        return "unsat",stats,None
    status,operations,chosen=majority_assignment(*pairwise,max_pc_vars=max_pc_vars)
    if status in ("cap","skip"):
        stats["reason"]="cap" if status=="cap" else "no_majority"
        return "skip",stats,None
    if status=="unsat":
        return status,stats,None
    full=base.copy()
    for i,value in chosen.items():
        full.extend(rows[i][value])
    model=_sat(n,full)
    if model is None:
        raise AssertionError("compatible choices failed physical integration")
    raw=model[:inputs]
    for ports,entries,traces in factors:
        choice=traces[tuple(model[v] for v in ports)]
        for v,b in zip(entries,choice):
            if v<inputs:
                raw[v]=b
    material=_replay(raw,physical)
    wires=_replay(raw,gates)
    if any(value!=((0 if base_id==-1 else material[expanded[base_id]])^s)
           for value,(base_id,s) in zip(wires,aliases)):
        raise AssertionError("original wire alias failed replay")
    if any(not any(material[abs(l)-1]==(l>0) for l in row) for row in full):
        raise AssertionError("materialized row replay failed")
    if any(not any(wires[abs(l)-1]==(l>0) for l in row) for row in original):
        raise AssertionError("original exterior replay failed")
    return "sat",stats,tuple(raw)
