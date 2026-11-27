"""Decide whether at most k AND gates are junk, with independent certificates.

Input JSON: {"n": 3, "edges": [[0,1]], "gates": [{"op":"and","inputs":[0,2]}], "k":1}.
At most k junk gates: list them all. Otherwise list the first k+1 in gate order.
Only raw IDs used by gate pins (r <= 2m for m gates) are enumerated.
For fixed K and binary input length L, at most sum(i<=K+2) binom(r,i)
supports are examined, each in polynomial bit time in L. All sparse maps
have polynomially many entries even with worst-case hash collisions.
"""
from itertools import combinations
import json
import sys


def natural(x):
    if type(x) is not int or x < 0:
        raise ValueError("expected a natural number")
    return x


def array(value):
    if type(value) is not list:
        raise ValueError("expected a JSON array")
    return value


def pair(value):
    if len(array(value)) != 2:
        raise ValueError("expected a pair")
    return tuple(map(natural, value))


def classify(n, edges, gates, k):
    n, k = natural(n), natural(k)
    graph = set()
    for edge in array(edges):
        a, b = pair(edge)
        if max(a, b) >= n or a == b:
            raise ValueError("expected a simple graph on the input wires")
        graph.add((min(a,b),max(a,b)))
    ops = []
    raw = set()
    for index, g in enumerate(array(gates)):
        if type(g) is not dict or set(g) != {"op","inputs"}:
            raise ValueError("expected a gate with op and inputs fields")
        a, b = pair(g["inputs"])
        if max(a,b) >= n+index or g["op"] not in ("and","or"):
            raise ValueError("expected exact AO2 with backward reads")
        raw.update(w for w in (a,b) if w < n)
        ops.append((g["op"],a,b))
    raw = sorted(raw)
    positive = {}
    if k:
        for size in range(1, min(len(raw),k+1)+1):
            for chosen in combinations(raw,size):
                if any(edge in graph for edge in combinations(chosen,2)):
                    continue
                true = set(chosen)
                for index,(op,a,b) in enumerate(ops):
                    if op == "and":
                        bit = a in true and b in true
                        if bit and index not in positive:
                            positive[index] = chosen
                    else:
                        bit = a in true or b in true
                    if bit:
                        true.add(n+index)
    return [{"gate": index, "support": positive[index]} for index in sorted(positive)[:k]]


def recognize(n, edges, gates, k):
    k = natural(k)
    witnesses = classify(n, edges, gates, k+1)
    return {"at_most_k": len(witnesses) <= k, "k": k, "witnesses": witnesses}


if __name__ == "__main__":
    try:
        record = json.load(sys.stdin)
        if type(record) is not dict or set(record) != {"n","edges","gates","k"}:
            raise ValueError("expected fields n, edges, gates and k")
        print(json.dumps(recognize(**record)))
    except ValueError as error:
        sys.exit(str(error))
