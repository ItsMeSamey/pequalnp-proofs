"""White-box PIT for affine-factor trees via spans of realized message vectors."""
from itertools import product
from random import Random
from check import parity, span, value


def independent(rows):
    pivots = {}
    keep = []
    for original in rows:
        row = list(original)
        for i in sorted(pivots):
            c = row[i]
            row = [(v-c*w)%3 for v,w in zip(row,pivots[i])]
        if any(row):
            i = next(i for i,v in enumerate(row) if v)
            pivots[i] = [(v*pow(row[i],-1,3))%3 for v in row]
            keep.append(original)
    return keep


def test(d, fs):
    owners = [[] for _ in fs]
    covered = {0}
    for i,(rows,_) in enumerate(fs):
        for r in rows:
            if r not in covered:
                owners[i].append(r)
                covered |= {v^r for v in covered}

    def solve(ids):
        ins = set(ids)
        A = span([r for i in ids for r in fs[i][0]])
        E = span([r for i in range(len(fs)) if i not in ins for r in fs[i][0]])
        boundary = sorted(A&E)
        if len(ids) == 1:
            i = ids[0]
            candidates = []
            for values in product((0,1),repeat=len(owners[i])):
                keep = [x for x in range(1 << d) if value(fs[i],x) and all(b or parity(r&x)==0 for r,b in zip(owners[i],values))]
                candidates.append([sum((-1)**parity(s&x) for x in keep)*pow(1<<d,-1,3)%3 for s in boundary])
        else:
            cut = len(ids)//2
            L, left = solve(ids[:cut])
            R, right = solve(ids[cut:])
            rid = {s:j for j,s in enumerate(R)}
            candidates = ([sum(x[j]*y[rid[a^s]] for j,a in enumerate(L) if a^s in rid)%3 for s in boundary] for x in left for y in right)
        return boundary, independent(candidates)

    _, basis = solve(list(range(len(fs))))
    return bool(basis)


rng = Random(417)
for _ in range(100):
    d = rng.randrange(1,7)
    fs = []
    for _ in range(rng.randrange(1,8)):
        rows = [rng.randrange(1<<d) for _ in range(rng.randrange(1,4))]
        fs.append((rows,[rng.randrange(2) for _ in range(1<<len(rows))]))
    assert test(d,fs) == any(all(value(f,x) for f in fs) for x in range(1<<d))
print("100 deterministic F3 message-span PIT tests matched SAT")
