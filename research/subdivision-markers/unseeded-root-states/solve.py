"""Construct the protected-root augmented matrix and exactly merge possible trace subspaces."""

def xor(values):
    total = 0
    for v in values:
        total ^= v
    return total


def image(columns, mask):
    return xor(c for i,c in enumerate(columns) if mask >> i & 1)


def eliminate(cols):
    pivots, relations = {}, []
    for i, v in enumerate(cols):
        coeff = 1 << i
        while v:
            j = v.bit_length()-1
            if j not in pivots:
                pivots[j] = (v,coeff)
                break
            row, used = pivots[j]
            v, coeff = v^row, coeff^used
        if not v:
            relations.append(coeff)
    return pivots,relations


def solve(cols, target):
    pivots,_ = eliminate(cols)
    coeff = 0
    while target:
        entry = pivots.get(target.bit_length()-1)
        if entry is None:
            return None
        row, used = entry
        target, coeff = target^row, coeff^used
    return coeff


def canonical(cols):
    pivots,_ = eliminate(cols)
    rows = {}
    for j,(v,_) in sorted(pivots.items()):
        for k,row in reversed(list(rows.items())):
            if v >> k & 1:
                v ^= row
        rows[j] = v
    return tuple(rows.values())


def intersection(a,b):
    a,b = tuple(a),tuple(b)
    _,deps = eliminate(a+b)
    return canonical(image(a,dep) for dep in deps)


def functional(cols, bits):
    pivots, deps = eliminate(cols)
    parity = lambda v: v.bit_count() & 1
    if any(parity(bits & dep) for dep in deps):
        return None
    answer = 0
    for j,(row,coeff) in sorted(pivots.items()):
        if parity(coeff & bits) != parity(answer & row):
            answer |= 1 << j
    return answer


def augment(base, primal, dual, t):
    r = max((x.bit_length() for x in base), default=0)
    ordinary = tuple(x ^ (gain<<r) for x,gain in zip(base,primal,strict=True))
    roots = tuple(1<<(r+i) for i in range(t)) + tuple(
        xor(x for x,gain in zip(base,dual,strict=True) if gain>>i & 1)
        for i in range(t))
    return ordinary, roots


def traces(ordinary, roots):
    peak_width = peak_states = 0

    def visit(lo,hi,outside):
        nonlocal peak_width, peak_states
        local = canonical(ordinary[lo:hi])
        port = intersection(local,outside)
        if hi==lo:
            table = {():0}
        elif hi==lo+1:
            table = {():0}
            table.setdefault(intersection(local,port),1<<lo)
        else:
            mid = (lo+hi)//2
            left = visit(lo,mid,canonical(outside+ordinary[mid:hi]))
            right = visit(mid,hi,canonical(outside+ordinary[lo:mid]))
            table = {}
            for a, ca in left.items():
                for b, cb in right.items():
                    new = intersection(a+b,port)
                    table.setdefault(new,ca|cb)
        peak_width=max(peak_width,len(port))
        peak_states=max(peak_states,len(table))
        return table

    table = visit(0,len(ordinary),canonical(roots))
    return table,peak_width,peak_states


def spectrum(base, primal, dual, t):
    ordinary, roots = augment(base,primal,dual,t)
    table,width,peak = traces(ordinary,roots)
    found = {}
    for trace, mask in table.items():
        selected = [i for i in range(len(base)) if mask>>i & 1]
        columns = tuple(ordinary[i] for i in selected)
        for a in range(1<<t):
            target = image(roots,a)
            if solve(trace,target) is None:
                continue
            local = solve(columns,target)
            assert local is not None
            c = sum(1<<i for j,i in enumerate(selected) if local>>j & 1)
            for b in range(1<<t):
                if a^b in found:
                    continue
                # First constrain root scores, then zero on all selected columns.
                alpha = functional(roots+columns,b<<t)
                if alpha is not None:
                    d = sum(((alpha & oe).bit_count()%2)<<i for i,oe in enumerate(ordinary))
                    assert not c&d and image(base,c)==0
                    assert image(primal,c)==a and image(dual,d)==b
                    found[a^b]=(c,d)
    return found,width,peak
