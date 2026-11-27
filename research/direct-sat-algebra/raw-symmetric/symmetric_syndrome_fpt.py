"""Deterministic typed exterior-algebra compression for symmetric principal minors."""
from itertools import combinations


def bits(mask):
    while mask:
        bit = mask & -mask
        yield bit.bit_length() - 1
        mask ^= bit


def dot(x, y):
    return (x & y).bit_count() % 2


def basis(vectors):
    pivots = {}
    for v in vectors:
        while v:
            j = v.bit_length() - 1
            if j not in pivots:
                pivots[j] = v
                break
            v ^= pivots[j]
    return pivots


def kernel(n, vectors):
    eq = basis(vectors)
    result = []
    for j in range(n):
        if j in eq:
            continue
        v = 1 << j
        for k in sorted(eq):
            v |= dot(eq[k], v) << k
        result.append(v)
    return result


def image(rows, vector):
    out = 0
    for i in bits(vector):
        out ^= rows[i]
    return out


def exists(rows, labels, target):
    n = len(rows)
    if len(labels) != n or target < 0 or any(x < 0 for x in labels):
        raise ValueError("invalid labels")
    if any(not 0 <= x < 1 << n for x in rows):
        raise ValueError("invalid rows")
    if any((rows[i] >> j ^ rows[j] >> i) & 1 for i, j in combinations(range(n), 2)):
        raise ValueError("expected symmetric matrix")
    equations = basis(sum(((v >> i) & 1) << (j+1) for j,v in enumerate(labels))
                      | (target >> i & 1) for i in range(max([target,*labels]).bit_length()))
    if 0 in equations:
        return False
    eq = list(equations.values())
    tags = [sum((r >> (i+1) & 1) << j for j,r in enumerate(eq)) for i in range(n)]
    groups = {a:[i for i,v in enumerate(tags) if v==a] for a in sorted(set(tags))}
    diag = sum((rows[i] >> i & 1) << i for i in range(n))
    masks = {a:sum(1 << i for i in ix) for a,ix in groups.items()}
    low = {a:basis([diag & mask]) for a,mask in masks.items()}
    pairs = list(combinations(groups,2))
    p = len(pairs)
    high = []
    ranked = []
    for a,b in pairs:
        row_space = basis(rows[i] & masks[b] for i in groups[a])
        ranked.append((len(row_space),a,b,row_space))
    for rank,a,b,space in sorted(ranked):
        d = sum(map(len,low.values()))
        if rank > 4*d+4*p:
            high.append((a,b))
            continue
        low[b] = basis([*low[b].values(), *space.values()])
        low[a] = basis([*low[a].values(), *(rows[i] & masks[a] for i in groups[b])])
    vectors = [(a,1 << i) for a in groups for i in low[a]]
    for a,b in high:
        def candidates(t):
            ix = groups[t]
            constraints = list(low[t].values())
            constraints += [image(rows,v) & masks[t] for s,v in vectors if s != t]
            packed = [sum((c >> i & 1) << j for j,i in enumerate(ix)) for c in constraints]
            return [sum(1 << ix[j] for j in bits(v)) for v in kernel(len(ix),packed)]
        left,right = candidates(a),candidates(b)
        for x in left:
            row = image(rows,x)
            y = next((z for z in right if dot(row,z)),0)
            if y:
                vectors.extend([(a,x),(b,y)])
                break
        else:
            raise AssertionError("rank separation failed")
    marked = [(1 << i,a) for i,(a,x) in enumerate(vectors) if dot(x,diag)]
    for i,(a,x) in enumerate(vectors):
        row = image(rows,x)
        for j,(b,y) in enumerate(vectors[:i]):
            if a!=b and dot(row,y):
                marked.append(((1<<i)|(1<<j),a^b))
    value = {0}
    for j,r in enumerate(eq):
        h = sum(((a>>j)&1)<<i for i,(a,x) in enumerate(vectors))
        next_value = {m for m in value if (1 ^ (r&1) ^ dot(m,h))}
        for term,tag in marked:
            if tag>>j&1:
                for m in value:
                    if not m & term:
                        next_value.symmetric_difference_update([m|term])
        value = next_value
    return bool(value)


def witness(rows, labels, target):
    if not exists(rows,labels,target):
        return None
    keep = list(range(len(rows)))
    for i in range(len(rows)):
        ix = [j for j in keep if j != i]
        restricted = [sum((rows[j]>>v&1)<<k for k,v in enumerate(ix)) for j in ix]
        if exists(restricted,[labels[j] for j in ix],target):
            keep = ix
    return sum(1<<i for i in keep)


if __name__ == "__main__":
    from symmetric_syndrome import invertible
    from random import Random
    rng = Random(123)
    for n in range(8):
        for trial in range(10):
            rows = [0]*n
            for i in range(n):
                for j in range(i+1):
                    if rng.getrandbits(1):
                        rows[i] |= 1<<j
                        rows[j] |= 1<<i
            labels = [rng.randrange(4) for _ in rows]
            live = set()
            for m in range(1<<n):
                if invertible([rows[i]&m for i in bits(m)]):
                    s=0
                    for i in bits(m):
                        s ^= labels[i]
                    live.add(s)
            for u in range(4):
                m = witness(rows,labels,u)
                assert (m is not None)==(u in live)
                if m is not None:
                    s=0
                    for i in bits(m):
                        s ^= labels[i]
                    assert s==u and invertible([rows[i]&m for i in bits(m)])
    # Three rank-20 pair blocks sharing type spaces, zero loop forms.
    n=60
    rows=[sum(1<<(20*b+i%20) for b in range(3) if b!=i//20) for i in range(n)]
    labels=[1<<(i//20) for i in range(n)]
    for u in range(8):
        assert exists(rows,labels,u)==(u.bit_count()%2==0)
    print("320 exhaustive comparisons, witness replays, eight high-rank decisions")
