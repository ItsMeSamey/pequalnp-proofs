"""Compile small-rank, possibly overlapping XOR features to an ordinary multilinear DAG."""
import argparse
import json
from interface_compiler import Arithmetic, compile_dag as generic, parse


def compile_affine(spec, p, rank_cap=8):
    if type(rank_cap) is not int or rank_cap < 0:
        raise ValueError("rank_cap must be a nonnegative integer")
    # Use the same parser and prime validation as the general compiler.
    generic({"inputs":[],"gates":[["const",0]],"output":0}, p)
    gates, output = parse(spec)
    names = spec["inputs"]
    positions = {x:i for i,x in enumerate(names)}
    forms = []
    for g in gates:
        if g[0] == "var":
            form = (1 << positions[g[1]], 0)
        elif g[0] == "const":
            form = (0, g[1])
        else:
            _, mask, a, b = g
            f, h, j, k = [(mask >> i) & 1 for i in range(4)]
            form = None
            if not (f ^ h ^ j ^ k):
                bits, const = 0, f
                for coeff, child in ((f ^ j, a), (f ^ h, b)):
                    if coeff:
                        if forms[child] is None:
                            break
                        cbits, cconst = forms[child]
                        bits ^= cbits
                        const ^= cconst
                else:
                    form = (bits, const)
        forms.append(form)

    frontier, upper, pending = set(), set(), [output]
    while pending:
        i = pending.pop()
        if i in frontier or i in upper:
            continue
        if forms[i] is not None:
            frontier.add(i)
        else:
            upper.add(i)
            pending.extend(gates[i][2:])

    # Pivots are reduced raw linear forms. Their independent truth values
    # are syndrome coordinates; eliminate each boundary form in this basis.
    pivots, basis, reps = {}, [], {}
    for i in sorted(frontier):
        row, const = forms[i]
        coords = 0
        while row:
            lead = row.bit_length() - 1
            if lead not in pivots:
                j = len(basis)
                if j >= rank_cap:
                    result = generic(spec,p)
                    result["stats"]["route"] = "interface"
                    result["stats"]["affine_rank_lower_bound"] = j+1
                    return result
                pivots[lead] = j
                basis.append(row)
            j = pivots[lead]
            row ^= basis[j]
            coords ^= 1 << j
        reps[i] = (coords,const)
    rank = len(basis)
    ar = Arithmetic(p)
    upper = sorted(upper)
    states = []
    for sigma in range(1 << rank):
        values = {i: ((mask & sigma).bit_count() & 1) ^ c for i,(mask,c) in reps.items()}
        for i in upper:
            _, mask, a, b = gates[i]
            values[i] = (mask >> (2*values[a]+values[b])) & 1
        states.append(ar.const(values[output]))

    groups = {}
    for j, name in enumerate(names):
        effect = sum(((row >> j)&1) << k for k,row in enumerate(basis))
        if effect:
            groups.setdefault(effect, []).append(name)
    for effect, group in groups.items():
        # Each group consumes fresh RAW variables; do not multiply affine
        # forms whose original supports intersect.
        parity = ar.node("var",group[0])
        for name in group[1:]:
            new = ar.node("var",name)
            parity = ar.truth(6,parity,new)
        previous = states
        states = []
        for sigma, low in enumerate(previous):
            high = previous[sigma ^ effect]
            if low == high:
                value = low
            else:
                delta = ar.op("add",high,ar.scale(-1,low))
                value = ar.op("add",low,ar.op("mul",parity,delta))
            states.append(value)
    out = states[0]
    needed = {out}
    for i in range(out,-1,-1):
        if i in needed and ar.nodes[i][0] in ("add","mul"):
            needed.update(ar.nodes[i][1:])
    ids, emitted = {}, []
    for i in sorted(needed):
        node = ar.nodes[i]
        if node[0] in ("add","mul"):
            node = (node[0],ids[node[1]],ids[node[2]])
        ids[i] = len(emitted)
        emitted.append(node)
    return {"nodes":emitted, "output":ids[out], "stats":{
        "route":"affine", "rank":rank, "groups":len(groups),
        "allocated_nodes":len(ar.nodes),"emitted_nodes":len(emitted),
        "emitted_operations":sum(g[0] in ("add","mul") for g in emitted),
        "state_updates":len(groups)*(1<<rank)}}


if __name__ == "__main__":
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument("file")
    cli.add_argument("--prime", type=int, default=2)
    cli.add_argument("--rank-cap", type=int, default=8)
    args=cli.parse_args()
    with open(args.file,encoding="utf-8") as f:
        print(json.dumps(compile_affine(json.load(f),args.prime,args.rank_cap)))
