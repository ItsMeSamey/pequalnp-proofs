"""Two charged K4 incidence gadgets with a balanced K4,4 core."""
from itertools import combinations, permutations

def bit(i):
    return 1 << i

core = [(p,h) for h in range(4) for p in range(4) if p != h]
extra = [(4,0),(4,1)]
edges = core + extra
all_edges = edges + [(h,h) for h in range(4)]
aux_edges = list(combinations(range(4), 2))
starts = [14,24]
marker = bit(12) | bit(13)
rows = []
for h in range(4):
    prefix = sum(bit(i) for i,(p,_) in enumerate(core) if p == h)
    for i,e in enumerate(edges):
        if e[1] == h:
            shift = 0 if i < 12 else bit(starts[i-12])
            rows.append((bit(i),prefix ^ shift,1))
            prefix ^= bit(i)
stars = [sum(bit(i) for i,e in enumerate(aux_edges) if v in e) for v in range(4)]
for j,s in enumerate(starts):
    block = [(bit(s+v),(stars[v] << (s+4)) ^ (bit(12+j) if v == 0 else 0),0)
             for v in range(4)]
    block += [(bit(s+4+i),bit(s+u)|bit(s+v),0) for i,(u,v) in enumerate(aux_edges)]
    terms = set()
    for pivot,mask,_ in block:
        for i in range(34):
            if mask & bit(i):
                terms.symmetric_difference_update({pivot|bit(i)})
    assert terms == {bit(s)|bit(12+j)}
    rows.extend(block)
rows.append((0,marker,1))  # Pivot zero designates the mandatory affine row.

def certify_pin(i, value):
    constants = {}
    if i < len(edges):
        p,h = edges[i]
        if value:
            constants = {e:int(e == (p,h)) for e in all_edges if e[0] == p or e[1] == h}
        else:
            constants[edges[i]] = 0
    if value and i in starts:
        constants[extra[starts.index(i)]] = 0
    aux_fixed = bit(i) if value and i >= len(edges) else 0
    remaining = [e for e in all_edges if e not in constants]
    assert len({p for p,h in remaining}) == len({h for p,h in remaining})+1
    def image_edge(e):
        if e in constants:
            return {0} if constants[e] else set()
        return {bit(remaining.index(e))}
    def image(k):
        if k < len(edges):
            return image_edge(edges[k])
        return {0} if aux_fixed & bit(k) else set()
    assert image(i) == ({0} if value else set())
    def product(a,b):
        out = set()
        for x in a:
            for y in b:
                out.symmetric_difference_update({x|y})
        return out
    basis = {}
    def reduce(poly):
        while poly and max(poly) in basis:
            poly ^= basis[max(poly)]
        return poly
    def add(poly):
        poly = reduce(poly)
        if poly:
            basis[max(poly)] = poly
    for a,b in combinations(all_edges,2):
        if a[0] == b[0] or a[1] == b[1]:
            add(product(image_edge(a),image_edge(b)))
    for p in range(5):
        clause = {0}
        for e in all_edges:
            if e[0] == p:
                clause ^= image_edge(e)
        add(clause.copy())
        for k in range(len(remaining)):
            add(product(clause,{bit(k)}))
    for pivot,mask,offset in rows:
        affine = {0} if offset else set()
        for k in range(34):
            if mask & bit(k):
                affine ^= image(k)
        row = product(image(pivot.bit_length()-1),affine) if pivot else affine
        assert not reduce(row), (i,value,pivot,mask)
for i in range(34):
    for value in (0,1):
        certify_pin(i,value)

# At width three K4 minus a queried set has a component with >2 vertices.
from collections import Counter
distributions = {}
for scope in range(64):
    if scope.bit_count() > 3:
        continue
    components = [{v} for v in range(4)]
    for k,(u,v) in enumerate(aux_edges):
        if scope & bit(k):
            continue
        a,b = (next(c for c in components if x in c) for x in (u,v))
        if a != b:
            components.remove(b)
            a.update(b)
    giant, = [c for c in components if len(c)>2]
    for defect in giant:
        counts = Counter(z & scope for z in range(64)
                         if all((z & star).bit_count()%2 == ((v == 0) ^ (v == defect))
                                for v,star in enumerate(stars)))
        assert counts == distributions.setdefault(scope,counts)
    for k in range(6):
        if scope & bit(k):
            child = scope ^ bit(k)
            projected = Counter()
            for assignment,weight in counts.items():
                projected[assignment & child] += weight
            assert projected == distributions[child]
covered = set()
for active,s in enumerate(starts):
    inactive = starts[1-active]
    free = 63 << (s+4)
    for match in permutations(range(4)):
        base = sum(bit(i) for i,(p,h) in enumerate(core) if match[p] == h)
        for inactive_z in (0,63):
            fixed = base | bit(12+active) | (15 << s) | (inactive_z << (inactive+4))
            for pivot,mask,offset in rows:
                scope = ((mask|pivot) & free) >> (s+4)
                for z in distributions[scope]:
                    assignment = fixed | (z << (s+4))
                    if not pivot or pivot & assignment:
                        assert (mask & assignment).bit_count()%2 == offset
            covered.update((i,bool(bit(i)&fixed)) for i in range(34) if not bit(i)&free)
assert len(covered) == 68
print("Both charged sums, 42 K4 marginals, 68 pinned SA faces and 68 residual PC simulations passed.")
