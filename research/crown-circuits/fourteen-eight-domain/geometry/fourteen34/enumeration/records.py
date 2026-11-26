"""Extract maximal OR groups and replay their size-preserving physical expansion."""
import argparse
import json
from pathlib import Path


def extract(circuit):
    n, gates, output = circuit["inputs"], circuit["gates"], circuit["output"]
    uses = [[] for _ in range(n + len(gates))]
    for node, (op, a, b) in enumerate(gates, n):
        if op not in ("AND", "OR") or not (0 <= a < node and 0 <= b < node):
            raise ValueError("invalid gate")
        uses[a].append(node)
        uses[b].append(node)
    uses[output].append(None)
    if any(not slots for slots in uses[n:]):
        raise ValueError("dead gate")
    if any(len(slots) != 2 or any(j is None or gates[j-n][0] != "OR" for j in slots)
           for slots in uses[:n]):
        raise ValueError("irregular raw input")

    merged = set()
    for node, (op, a, b) in enumerate(gates, n):
        slots = uses[node]
        if op == "OR" and len(slots) == 1 and slots[0] is not None:
            if gates[slots[0] - n][0] == "OR":
                merged.add(node)
    rows, identifiers = [], {}

    def flatten(node):
        if node not in merged:
            return [node]
        _, a, b = gates[node-n]
        return flatten(a) + flatten(b)

    for node, (op, a, b) in enumerate(gates, n):
        if node in merged:
            continue
        terms = flatten(a) + flatten(b) if op == "OR" else [a,b]
        identifiers[node] = len(rows)
        rows.append(dict(op=op, raw=sorted(z for z in terms if z<n),
                         parents=sorted(identifiers[z] for z in terms if z>=n)))
    return dict(inputs=n, rows=rows, output=identifiers[output])


def expand(record):
    n = record["inputs"]
    gates, roots = [], []
    for row in record["rows"]:
        terms = row["raw"] + [roots[j] for j in row["parents"]]
        if len(terms)<2 or (row["op"]=="AND" and (row["raw"] or len(terms)!=2)):
            raise ValueError("invalid row")
        wire = terms[0]
        for other in terms[1:]:
            gates.append([row["op"], wire, other])
            wire = n + len(gates) - 1
        roots.append(wire)
    return dict(inputs=n, gates=gates, output=roots[record["output"]])


def evaluate(circuit, cases):
    n = circuit["inputs"]
    values = [sum(((x>>i)&1)<<j for j,x in enumerate(cases)) for i in range(n)]
    for op,a,b in circuit["gates"]:
        values.append(values[a]&values[b] if op=="AND" else values[a]|values[b])
    return values[circuit["output"]]


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("circuit", type=Path)
    parser.add_argument("--record", type=Path)
    args=parser.parse_args()
    src=json.loads(args.circuit.read_text())
    rec=extract(src)
    dst=expand(rec)
    n=src["inputs"]; cases=range(1<<n)
    target=sum(1<<x for x in cases if x.bit_count()>=2)
    if evaluate(src,cases)!=target or evaluate(dst,cases)!=target:
        raise ValueError("truth replay failed")
    if len(src["gates"])!=len(dst["gates"]):
        raise ValueError("gate count changed")
    rows=rec["rows"]
    q=sum(bool(r["raw"]) for r in rows)
    p=sum(r["op"]=="OR" and not r["parents"] for r in rows)
    z=sum(r["op"]=="OR" and not r["raw"] for r in rows)
    a=sum(r["op"]=="AND" for r in rows)
    cost=sum(len(r["parents"])-1 for r in rows if r["op"]=="OR" and r["parents"])
    if cost!=len(dst["gates"])-a-2*n+p:
        raise ValueError("ledger failed")
    if args.record: args.record.write_text(json.dumps(rec,indent=2)+"\n")
    print(f"{len(cases)} assignments; {len(dst['gates'])} gates; {a} AND; {q} raw groups; {p} pure; {z} auxiliary OR groups; {cost} nonraw mergers")


if __name__=="__main__":
    main()
