"""Count assignments avoiding forbidden affine flats on a supplied binary clause tree."""


def eliminate(rows):
    pivots = {}
    for mask, rhs in rows:
        while mask:
            p = mask.bit_length()
            if p not in pivots:
                pivots[p] = (mask,rhs)
                break
            a,b = pivots[p]
            mask ^= a
            rhs ^= b
        if not mask and rhs:
            return None
    return pivots


def basis(rows):
    return [a for a,_ in eliminate((m,0) for m in rows).values()]


def intersection(left, right):
    # Track the right-hand component of each dependence in left+right.
    pivots = {}
    both = []
    for vector, tag in [(a,0) for a in left] + [(b,b) for b in right]:
        while vector:
            p = vector.bit_length()
            if p not in pivots:
                pivots[p] = (vector,tag)
                break
            a,b = pivots[p]
            vector ^= a
            tag ^= b
        if not vector and tag:
            both.append(tag)
    return basis(both)


def equations(rows, value):
    return [(row, value >> i & 1) for i,row in enumerate(rows)]


def compute(n, flats, tree, recover=False):
    """Flat consists of (mask,rhs) equations; tree is leaf index or nested pair.

    """
    if any(m < 0 or m.bit_length() > n or c not in (0,1) for f in flats for m,c in f):
        raise ValueError("invalid flat")
    spans = {}
    seen = []
    def build(t):
        if isinstance(t,int):
            seen.append(t)
            rows = [a for a,_ in flats[t]]
        else:
            rows = build(t[0]) + build(t[1])
        spans[t] = basis(rows)
        return spans[t]
    if not flats:
        return 0 if recover else 1 << n
    root = build(tree)
    if sorted(seen) != list(range(len(flats))):
        raise ValueError("tree must contain each flat exactly once")

    traces = {}
    def table(t, exterior):
        local = spans[t]
        boundary = intersection(local,exterior)
        if isinstance(t,int):
            values = []
            for i in range(1 << len(boundary)):
                eqs = equations(boundary,i)
                bad = eliminate(eqs + flats[t])
                total = 1 << (len(local)-len(boundary))
                excluded = 0 if bad is None else 1 << (len(local)-len(bad))
                values.append(total-excluded)
            traces[t] = boundary
            return boundary,values
        l,r = t
        lb,lv = table(l,basis(exterior + spans[r]))
        rb,rv = table(r,basis(exterior + spans[l]))
        joint = basis(lb + rb)
        # Every parent-boundary row belongs to the join of child boundaries.
        def coordinates(vector):
            # Encode vector expansion by carrying coordinate tags in elimination.
            mask = 0
            for j,row in sorted(enumerate(joint),key=lambda p:-p[1].bit_length()):
                if vector & (1 << (row.bit_length()-1)):
                    vector ^= row
                    mask ^= 1 << j
            assert vector == 0
            return mask
        def projection(rows):
            return [coordinates(a) for a in rows]
        def project(x, masks):
            return sum(((m & x).bit_count()%2) << j for j,m in enumerate(masks))
        pl,pr,po = map(projection,(lb,rb,boundary))
        values = [0] * (1 << len(boundary))
        choices = {}
        for x in range(1 << len(joint)):
            a,b,c = project(x,pl),project(x,pr),project(x,po)
            weight = lv[a]*rv[b]
            values[c] += weight
            if recover and weight:
                choices[c] = (a,b)
        traces[t] = choices
        return boundary,values
    total = table(tree,[])[1][0]
    if not recover:
        return total << (n-len(root))
    if not total:
        return None
    constraints = []
    def descend(t,i):
        if isinstance(t,int):
            eqs = equations(traces[t],i)
            for a,c in flats[t]:
                selected = eqs + [(a,c ^ 1)]
                if eliminate(selected) is not None:
                    constraints.extend(selected)
                    return
            raise AssertionError("positive leaf must allow a violated equation")
        a,b = traces[t][i]
        descend(t[0],a)
        descend(t[1],b)
    descend(tree,0)
    pivots = eliminate(constraints)
    assert pivots is not None
    x = 0
    for p,(a,c) in sorted(pivots.items()):
        x |= (c ^ ((a & x).bit_count() % 2)) << (p-1)
    return x
