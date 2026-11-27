"""Enumerate minimum AO2 lists for every nonempty graph through three inputs."""
from collections import Counter
from itertools import combinations
from pathlib import Path
import json


def measurements(n, edges, target, values, gates):
    inputs = [{i} for i in range(n)]
    or_cones = [set() for i in range(n)]
    cones = [set() for i in range(n)]
    tops, dirty, ors, ands = set(), set(), set(), set()
    for w, (op, a, b) in enumerate(gates, n):
        below = not (values[w] & ~target)
        cones.append({a, b} | cones[a] | cones[b])
        if op == 'and':
            ands.add(w)
            (tops if below else dirty).add(w)
            inputs.append(set())
            or_cones.append(set())
        else:
            if not below:
                ors.add(w)
            inputs.append(inputs[a] | inputs[b])
            or_cones.append({w} | or_cones[a] | or_cones[b])
    if any(cones[w] & tops for w in ands):
        return None
    star, lam, centreless = set(), set(), set()
    for w in tops:
        _, a, b = gates[w-n]
        if not inputs[a] or not inputs[b]:
            centreless.add(w)
        star.update(tuple(sorted((x,y))) for x in inputs[a] for y in inputs[b])
        for leaf, other in ((a,b),(b,a)):
            if len(inputs[other]) == 1:
                for h in or_cones[leaf] & ors:
                    _, x, y = gates[h-n]
                    if inputs[x] and inputs[y]:
                        lam.add(h)
    tau = min(mask.bit_count() for mask in range(1 << n)
              if all((mask >> x | mask >> y) & 1 for x,y in edges))
    left = tau + len(edges-star)
    right = len(tops-centreless) + 2*len(centreless) + len(dirty) + len(ors-lam)
    return left, right


def analyze(n, edges):
    ins = [sum(1 << x for x in range(1 << n) if x >> i & 1) for i in range(n)]
    target = sum(1 << x for x in range(1 << n)
                 if any((x >> a) & (x >> b) & 1 for a,b in edges))
    # A least list outputs its last gate; replacing a repeated truth function by
    # the earlier wire and deleting the redundant gate gives a shorter circuit.
    # Commuting operands preserves all measured sets; weight each gate by two
    # to count both orders. Repeated operands produce an earlier truth function.
    def visit(values, gates, depth, counter):
        if len(gates) == depth:
            if values[-1] == target:
                m = measurements(n, edges, target, values, gates)
                counter[m] += 2**depth
            return
        for a,b in combinations(range(len(values)),2):
            for op, v in (('and',values[a]&values[b]),('or',values[a]|values[b])):
                if v not in values:
                    visit(values+[v], gates+[(op,a,b)], depth, counter)
    for depth in range(1, 2*len(edges)):
        counter = Counter()
        visit(ins, [], depth, counter)
        if counter:
            return dict(n=n, edges=sorted(edges), size=depth, minima=sum(counter.values()),
                        non_top=counter[None], inequalities=[[*m,k] for m,k in counter.items() if m])
    raise ValueError("edge-by-edge upper bound failed")


if __name__ == '__main__':
    results = []
    for n in range(4):
        potential = list(combinations(range(n),2))
        for mask in range(1,1 << len(potential)):
            results.append(analyze(n,{e for i,e in enumerate(potential) if mask >> i & 1}))
    Path(__file__).with_name('small4186.json').write_text(json.dumps(results,indent=2)+'\n')
    for r in results:
        print(r)
