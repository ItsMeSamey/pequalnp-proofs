"""Check the conditional span, crossing guards, and suffix PC2 rank."""
from itertools import permutations, combinations

arcs = [(p,h) for p in range(3) for h in range(3) if h != p]
matching_vectors = [sum(1 << i for i,(p,h) in enumerate(arcs) if perm[p] == h)
                    for perm in permutations(range(3))]
K4 = list(combinations(range(4),2))
width = 17  # 6 core, 1 unmatched, 4 vertices, 6 switch edges per block


def guards(length):
    out = []
    for stage in range(length):
        base = width*stage
        e = base+6
        root = base+7
        for h in range(3):
            prefix = {base+i for i,(p,_) in enumerate(arcs) if p == h}
            if h == 0:
                shifted = prefix.copy()
                if stage:
                    shifted.add(root-width)
                out.append((e,shifted,1))
                prefix.add(e)
            for i,edge in enumerate(arcs):
                if edge[1] == h:
                    out.append((base+i,prefix.copy(),1))
                    prefix.add(base+i)
        for v in range(4):
            mask = {base+11+i for i,edge in enumerate(K4) if v in edge}
            if v == 0:
                mask.add(e)
            out.append((root+v,mask,int(v == 0)))
        for i,(u,v) in enumerate(K4):
            out.append((base+11+i,{root+u,root+v},0))
    return out


def rank(vectors):
    pivots = {}
    for row in vectors:
        while row:
            lead = row.bit_length()-1
            if lead not in pivots:
                pivots[lead] = row
                break
            row ^= pivots[lead]
    return len(pivots)


for length in range(1,9):
    rows = guards(length)
    monomials = {}
    vectors = []
    for p,mask,_ in rows:
        vector = 0
        for q in mask - {p}:
            term = tuple(sorted((p,q)))
            vector ^= 1 << monomials.setdefault(term,len(monomials))
        vectors.append(vector)
    assert rank(vectors) == width*length

old = guards(2)[width:width+7]
accepted = {}
for u in (0,1):
    for e in (0,1):
        accepted[u,e] = []
        for core in range(64):
            bits = (u << 7) | (core << width) | (e << (width+6))
            if all(not(bits >> p & 1) or
                   sum(bits >> k & 1 for k in mask)%2 == offset
                   for p,mask,offset in old):
                accepted[u,e].append(core)
assert not accepted[0,1]
assert set(accepted[0,0]) == set(matching_vectors)
assert set(accepted[1,0]) == set(matching_vectors)
assert 0 in accepted[1,1]
assert rank(accepted[1,0]+accepted[1,1]) == len(arcs)
for end in (1,2):
    for middle in ([],[3-end]):
        path = [end]+middle+[0]
        vector = sum(1 << arcs.index(edge) for edge in zip(path,path[1:]))
        assert vector in accepted[1,1]
print("Checked all 256 controlled core assignments and full PC2 quadratic ranks for chain lengths 1–8.")
