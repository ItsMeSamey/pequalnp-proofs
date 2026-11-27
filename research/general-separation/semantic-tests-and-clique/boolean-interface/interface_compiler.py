"""Compile topologically ordered Boolean truth-table DAGs to formal multilinear DAGs."""
import argparse
import itertools
import json
from math import isqrt


def parse(spec):
    names = spec["inputs"]
    if not isinstance(names, list) or not all(isinstance(x, str) for x in names) or len(set(names)) != len(names):
        raise ValueError("inputs must be distinct strings")
    gates = []
    for i, raw in enumerate(spec["gates"]):
        match raw:
            case ["var", x] if x in names:
                pass
            case ["const", c] if type(c) is int and c in (0, 1):
                pass
            case ["gate", mask, a, b] if all(type(k) is int for k in (mask, a, b)) and 0 <= mask < 16 and 0 <= a < i and 0 <= b < i:
                pass
            case _:
                raise ValueError(f"invalid gate {i}")
        gates.append(tuple(raw))
    out = spec["output"]
    if type(out) is not int or not 0 <= out < len(gates):
        raise ValueError("invalid output")
    return gates, out


class Arithmetic:
    def __init__(self, p):
        self.p = p
        self.nodes = []
        self.ids = {}

    def node(self, *key):
        if key not in self.ids:
            self.ids[key] = len(self.nodes)
            self.nodes.append(key)
        return self.ids[key]

    def const(self, c):
        return self.node("const", c % self.p)

    def op(self, kind, a, b):
        a, b = sorted((a, b))
        u, v = self.nodes[a], self.nodes[b]
        if u[0] == v[0] == "const":
            return self.const(u[1] + v[1] if kind == "add" else u[1] * v[1])
        for i, j in ((a, b), (b, a)):
            if self.nodes[i] == ("const", 0):
                return j if kind == "add" else i
            if kind == "mul" and self.nodes[i] == ("const", 1):
                return j
        return self.node(kind, a, b)

    def scale(self, c, a):
        return self.op("mul", self.const(c), a)

    def truth(self, mask, a, b):
        f, g, h, j = [(mask >> i) & 1 for i in range(4)]
        result = self.const(f)
        for coef, arg in ((h-f, a), (g-f, b)):
            if coef:
                result = self.op("add", result, self.scale(coef, arg))
        cross = j-h-g+f
        if cross % self.p:
            result = self.op("add", result, self.scale(cross, self.op("mul", a, b)))
        return result

    def interpolate(self, x, low, high):
        if low == high:
            return low
        delta = self.op("add", high, self.scale(-1, low))
        return self.op("add", low, self.op("mul", self.node("var", x), delta))


def compile_dag(spec, p, optimized=True):
    if type(p) is not int or p < 2 or any(p % d == 0 for d in range(2, isqrt(p) + 1)):
        raise ValueError("a prime modulus is required")
    gates, out = parse(spec)
    supports, interfaces = [], [set() for _ in gates]
    for gate in gates:
        if gate[0] == "gate":
            supports.append(supports[gate[2]] | supports[gate[3]])
        else:
            supports.append({gate[1]} if gate[0] == "var" else set())
    live = {out}
    for i in range(out, -1, -1):
        if i not in live or gates[i][0] != "gate":
            continue
        _, _, a, b = gates[i]
        live.update((a,b))
        common = supports[a] & supports[b]
        for child in (a,b):
            interfaces[child].update(common | (interfaces[i] & supports[child]))
    requests = [set() for _ in gates]
    requests[out].add(())
    if not optimized:
        for i in live:
            keys = sorted(interfaces[i])
            for values in itertools.product((None,0,1), repeat=len(keys)):
                requests[i].add(tuple((k,v) for k,v in zip(keys,values) if v is not None))

    def branches(a,b,context):
        pins = dict(context)
        shared = sorted((supports[a] & supports[b]) - pins.keys())
        for values in itertools.product((0,1), repeat=len(shared)):
            full = pins | dict(zip(shared,values))
            yield shared, tuple(sorted((k,v) for k,v in full.items() if k in supports[a])), tuple(sorted((k,v) for k,v in full.items() if k in supports[b]))

    for i in range(out, -1, -1):
        if gates[i][0] != "gate":
            continue
        _, _, a,b = gates[i]
        for ctx in requests[i]:
            for _, left,right in branches(a,b,ctx):
                requests[a].add(left)
                requests[b].add(right)

    ar = Arithmetic(p)
    cache = [{} for _ in gates]
    work = max_branch = 0
    for i,gate in enumerate(gates):
        for ctx in sorted(requests[i]):
            if gate[0] == "gate":
                _,mask,a,b = gate
                vals = []
                for shared,left,right in branches(a,b,ctx):
                    vals.append(ar.truth(mask,cache[a][left],cache[b][right]))
                work += len(vals)
                max_branch = max(max_branch,len(vals))
                for x in reversed(shared):
                    vals = [ar.interpolate(x,vals[j],vals[j+1]) for j in range(0,len(vals),2)]
                ans = vals[0]
            elif gate[0] == "var":
                x = gate[1]
                pins = dict(ctx)
                ans = ar.const(pins[x]) if x in pins else ar.node("var",x)
            else:
                ans = ar.const(gate[1])
            cache[i][ctx] = ans
    output = cache[out][()]
    needed = {output}
    for i in range(output, -1, -1):
        if i in needed and ar.nodes[i][0] in ("add", "mul"):
            needed.update(ar.nodes[i][1:])
    emitted = []
    index = {}
    for old in sorted(needed):
        node = ar.nodes[old]
        if node[0] in ("add", "mul"):
            node = (node[0], index[node[1]], index[node[2]])
        index[old] = len(emitted)
        emitted.append(node)
    return {"nodes":emitted,"output":index[output], "stats":{
        "emitted_nodes":len(emitted),
        "emitted_operations":sum(g[0] in ("add","mul") for g in emitted),
        "width":max(len(interfaces[i]) for i in live), "contexts":sum(map(len,requests)),
        "branches":work,"peak_branch_entries":max_branch,"allocated_nodes":len(ar.nodes),
        "field_operations":sum(g[0] in ("add","mul") for g in ar.nodes)}}


if __name__ == "__main__":
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("file",help="JSON source DAG")
    ap.add_argument("--prime",type=int,default=2)
    ap.add_argument("--eager",action="store_true")
    opts=ap.parse_args()
    with open(opts.file,encoding="utf-8") as f:
        source=json.load(f)
    print(json.dumps(compile_dag(source,opts.prime,not opts.eager)))
