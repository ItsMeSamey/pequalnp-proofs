"""Compare dirty-boundary score tables to direct global affine enumeration."""
from tree_check import (Random, defaultdict, product, widths, sizes, edges,
                        virtual, offsets, inc, ports, global_space, label, span, orth)

def dirty_table(i, parent, spaces, duals, a, b, h, j):
    mask = (1 << sizes[i]) - 1
    h_here, j_here = [(v >> offsets[i]) & mask for v in (h,j)]
    dirty = bool(h_here | j_here)
    dirty_slots = set()
    children = []
    for e, (u, v, _) in enumerate(edges):
        if u == i:
            table, dirty_child = dirty_table(v,e,spaces,duals,a,b,h,j)
            children.append((e,table))
            if dirty_child:
                dirty_slots.add(e)
                dirty = True
    if dirty:
        dirty_slots.add(parent)
    out = defaultdict(set)
    for x,y in product(spaces[i],duals[i]):
        actual_c = (x >> virtual[i]) ^ h_here
        actual_d = (y >> virtual[i]) ^ j_here
        if actual_c & actual_d:
            continue
        p,q = ports(i,x), ports(i,y)
        if any((w == 3 and p[e].bit_count()>1) or
               (e not in dirty_slots and p[e]&q[e]) for e,w in inc[i]):
            continue
        scores = {label(actual_c << offsets[i], a)^label(actual_d << offsets[i], b)}
        for e,table in children:
            scores = {v^u for v in scores for u in table[(p[e],q[e])]}
        out[(p.get(parent,0),q.get(parent,0))].update(scores)
    return out,dirty

def main():
    rng = Random(63781)
    n = sum(sizes)
    for trial in range(30):
        spaces = []
        for i,w in enumerate(widths):
            rows = [rng.randrange(1<<w) for _ in range(rng.randrange(1,4))]
            if i in (0,1):
                rows.append(7)
            spaces.append(span(rows))
        duals = [orth(s,w) for s,w in zip(spaces,widths)]
        a,b = [[1 << (i+shift) for i in range(n)] for shift in (0,n)]
        h,j = [sum(1 << i for i in rng.sample(range(n),2)) for _ in range(2)]
        C,D = global_space(spaces),global_space(duals)
        want = {(x^h) | ((y^j)<<n) for x,y in product(C,D) if not (x^h)&(y^j)}
        got = dirty_table(0,None,spaces,duals,a,b,h,j)[0][(0,0)]
        assert got == want, trial
    print("30 sparse affine tree instances: exact pair sets agree")
if __name__ == "__main__":
    main()
