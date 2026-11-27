"""Enumerate least connected AO2 gate lists for C4-free graphs on four vertices."""
from collections import Counter
from itertools import combinations
from small4186 import measurements

FAMILIES = {
    "edge": [(0,1)], "matching": [(0,1),(2,3)], "two-star": [(0,1),(0,2)],
    "triangle": [(0,1),(1,2),(0,2)], "claw": [(0,1),(0,2),(0,3)],
    "path": [(0,1),(1,2),(2,3)], "paw": [(0,1),(0,2),(1,2),(0,3)]}


def run():
    inputs = tuple(sum(1 << x for x in range(16) if x >> i & 1) for i in range(4))
    for name, edges in FAMILIES.items():
        target = 0
        for a,b in edges:
            target |= inputs[a] & inputs[b]
        count = Counter()
        def visit(values, gates, live, remaining):
            if len(live) > remaining + 1:
                return
            for a,b in combinations(range(len(values)),2):
                nxt = (live - {a,b}) | {len(values)}
                if len(nxt) > remaining:
                    continue
                for op,v in [('and',values[a]&values[b]), ('or',values[a]|values[b])]:
                    if v in values:
                        continue
                    if remaining == 1 and v != target:
                        continue
                    vs, gs = (*values,v), (*gates,(op,a,b))
                    if remaining > 1:
                        visit(vs,gs,nxt,remaining-1)
                    else:
                        m = measurements(4,set(edges),target,vs,gs)
                        dirty = sum(1 for i,(op,_,_) in enumerate(gs,4) if op=='and' and vs[i]&~target)
                        count[(m,dirty)] += 1
        for d in range(1,6):
            visit(inputs,(),set(),d)
            if count:
                print(name,d,dict(count),flush=True)
                break
        else:
            raise RuntimeError(name)
if __name__=='__main__':
    run()
