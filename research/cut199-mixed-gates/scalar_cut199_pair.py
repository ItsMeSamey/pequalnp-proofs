"""Independent scalar full-cube replay for the cut-199 control pair."""
import hashlib
import json
import sys
from pathlib import Path

CUT = 199
EDGES = {(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),
         (4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)}


def check(ok, message):
    if not ok:
        raise ValueError(message)


def replay(path):
    raw = Path(path).read_bytes()
    doc = json.loads(raw)
    if "edges" in doc:
        check({tuple(sorted(e)) for e in doc["edges"]} == EDGES, "wrong graph")
    check(doc.get("cut", CUT) == CUT, "wrong cut")
    check(doc.get("inputs", 11) == 11, "wrong input count")
    gates = []
    deps = [1 << i for i in range(11)]
    for w, (op, a, b) in enumerate(doc["gates"], 11):
        check(type(a) is int and type(b) is int and 0 <= a < w and 0 <= b < w,
              f"invalid earlier-wire reference at {w}")
        check(type(op) is bool or op in ("and", "or"), f"invalid opcode at {w}")
        gates.append((op is True or op == "and", a, b))
        deps.append(deps[a] | deps[b])
    out = doc["output"]
    check(type(out) is int and 0 <= out < len(deps), "invalid output")
    live = {out}
    for w in reversed(range(11, len(deps))):
        if w in live:
            live.update(gates[w-11][1:])
    check(set(range(11, len(deps))) <= live, "dead gate")
    values = [bytearray(2048) for _ in deps]
    target = bytearray(2048)
    for x in range(2048):
        vals = [bool(x & (1 << i)) for i in range(11)]
        for is_and, a, b in gates:
            vals.append((vals[a] and vals[b]) if is_and else (vals[a] or vals[b]))
        target[x] = any(vals[a] and vals[b] for a, b in EDGES)
        check(vals[out] == target[x], f"functional mismatch at raw input {x}")
        for w, bit in enumerate(vals):
            values[w][x] = bit
    names = ("pureLeft", "pureRight", "mixed")
    def classify(mask):
        if not mask & ~CUT:
            return names[0]
        if not mask & CUT:
            return names[1]
        return names[2]
    counts = {name: 0 for name in names}
    semantic = counts.copy()
    for w in range(11, len(deps)):
        counts[classify(deps[w])] += 1
        support = sum(1 << j for j in range(11)
                      if any(values[w][x] != values[w][x ^ (1 << j)] for x in range(2048)))
        semantic[classify(support)] += 1
    for name in names:
        check(doc.get(name, counts[name]) == counts[name], f"bad recorded {name}")
    outside = {w for w in range(11, len(deps))
               if any(bit and not goal for bit, goal in zip(values[w], target))}
    ands = {w for w, (is_and, _, _) in enumerate(gates, 11) if is_and}
    tops = ands - outside
    raw_reach = [{i} for i in range(11)]
    or_reach = [set() for _ in range(11)]
    ancestors = [set() for _ in range(11)]
    for w, (is_and, a, b) in enumerate(gates, 11):
        raw_reach.append(set() if is_and else raw_reach[a] | raw_reach[b])
        or_reach.append(set() if is_and else or_reach[a] | or_reach[b] | {w})
        ancestors.append(ancestors[a] | ancestors[b] | {a,b})
    star, paid_back = set(), set()
    centreless = 0
    for w in tops:
        _, a, b = gates[w-11]
        centreless += not(raw_reach[a] and raw_reach[b])
        star.update(tuple(sorted((i,j))) for i in raw_reach[a] for j in raw_reach[b] if i!=j)
        for side, other in [(a,b),(b,a)]:
            if len(raw_reach[other]) != 1:
                continue
            for v in or_reach[side] & outside:
                _, x, y = gates[v-11]
                if raw_reach[x] and raw_reach[y]:
                    paid_back.add(v)
    tau = min(mask.bit_count() for mask in range(2048)
              if all(mask & ((1<<a)|(1<<b)) for a,b in EDGES))
    q = len(outside - ands - paid_back)
    audit = dict(topform=not any(ancestors[w] & tops for w in ands),
                 lhs=tau + len(EDGES-star), rhs=len(tops)+centreless+len(ands&outside)+q,
                 u=len(EDGES-star), q=q)
    for name, value in doc.get("audit", {}).items():
        if name in audit:
            check(value == audit[name], f"bad recorded audit {name}")
    return dict(audit=audit, path=str(path), sha256=hashlib.sha256(raw).hexdigest(), total=len(gates),
                structural=counts, semantic=semantic, positive=sum(target),
                truth_sha256=hashlib.sha256(target).hexdigest())


if __name__ == "__main__":
    check(len(sys.argv) >= 2, "supply one or more witness JSON paths")
    print(json.dumps([replay(path) for path in sys.argv[1:]], indent=2))
