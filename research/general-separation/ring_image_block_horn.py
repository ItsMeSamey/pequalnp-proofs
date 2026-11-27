"""Blockwise affine recoding to Horn on simultaneous essential coordinates.

Ordered-image solve_sparse and solve_source_sparse return sorted original
true_ids on nonzero. Unknown only rejects this chart construction. Cost is
polynomial in the explicit forbidden tuples and compressed used-label size.
"""
from read_two_ring_image import recover
from ring_image_affine_hull_sparse import _closure, _combine
from itertools import combinations
from ring_image_common_basis import common_basis, span
from ring_image_coordinate_2sat import _insert, _lift
from ring_image_group_horn_strict import _rename
from ring_image_period_chart import essential_normals


def _centers(patterns, blocks):
    """Group identical observations. Each chosen center is an observed value."""
    observed = {sig:set() for sig in blocks}
    for pattern in patterns:
        for sig,value in pattern.items():
            observed[sig].add(value)
    tags, constraints = {}, []
    for sig,values in observed.items():
        if not values:
            continue
        origin = min(values)
        if len(span(v ^ origin for v in values).axes) != len(values)-1:
            return None, "dependent_block_values"
        for value in sorted(values):
            tags[sig,value] = len(tags)+1
        constraints.extend((-tags[sig,a], -tags[sig,b]) for a,b in combinations(sorted(values),2))
    for pattern in patterns:
        constraints.extend((tags[a,u],tags[b,v]) for (a,u),(b,v) in combinations(pattern.items(),2))
    # On pairs, _rename implements exactly the implications -a -> b, -b -> a.
    selected = _rename(list(tags.values()),constraints)
    if selected is None:
        return None, "no_block_centers"
    charts = {}
    for sig,values in observed.items():
        if not values:
            continue
        center = next((v for v in sorted(values) if tags[sig,v] in selected), min(values))
        basis = span(v ^ center for v in sorted(values) if v != center)
        for j in range(len(blocks[sig])):
            basis.append(1 << j)
        charts[sig] = center,basis
    return charts,None


def _horn(clauses):
    rules = []
    for row in clauses:
        heads = [v for v in row if v>0]
        if len(heads)>1:
            raise AssertionError("invalid block Horn certificate")
        rules.append(({-v for v in row if v<0}, heads[0] if heads else None))
    true = set()
    while True:
        old = len(true)
        for body,head in rules:
            if body <= true:
                if head is None:
                    return None
                true.add(head)
        if len(true)==old:
            return true


def solve_source_sparse(arity, signed_clauses):
    rows = tuple(tuple(row) for row in signed_clauses)
    if type(arity) is not int or arity < 0 or any(
            type(l) is not int or not 1 <= abs(l) <= arity for row in rows for l in row):
        raise ValueError("invalid arity or signed literal")
    used = sorted({abs(l) for row in rows for l in row})
    index = {v:i for i,v in enumerate(used)}
    groups = {}
    for row in rows:
        lits = set(row)
        if any(-l in lits for l in lits):
            continue
        names = sorted(map(abs,lits))
        scope = tuple(index[v] for v in names)
        groups.setdefault(scope,set()).add(sum(1 << j for j,v in enumerate(names) if -v in lits))
    eq, projected = _closure(groups)
    if eq is None:
        return dict(status="zero")
    spaces = [[_combine(projection.axes,v) for v in essential_normals(words,len(projection.axes))]
              for projection,words in projected]
    free = [1 << i for i in range(len(used)) if i not in eq]
    chart = common_basis(len(used), [*spaces,free])
    if chart is None:
        return dict(status="unknown",reason="incompatible_spaces")
    axes, signatures = chart
    tuples = []
    for i,(projection,words) in enumerate(projected):
        ids = [j for j,t in enumerate(signatures,1) if t >> i & 1]
        local = []
        for j in ids:
            rem, code = projection.decompose(axes[j-1])
            if rem:
                raise AssertionError("axis outside its projection row space")
            local.append(code)
        masks = {sum(((code & w).bit_count() % 2) << t for t,code in enumerate(local))
                 for w in words}
        tuples.append((ids,masks))
    blocks = {}
    for j, signature in enumerate(signatures, 1):
        blocks.setdefault(signature, []).append(j)
    patterns = []
    for i, (ids, masks) in enumerate(tuples):
        position = {v:j for j,v in enumerate(ids)}
        for mask in sorted(masks):
            patterns.append({sig:sum(((mask >> position[v]) & 1) << k
                                     for k,v in enumerate(block))
                             for sig,block in blocks.items() if sig & (1 << i)})
    charts, reason = _centers(patterns, blocks)
    if reason:
        return dict(status="unknown", reason=reason)
    clauses = []
    for pattern in patterns:
        row = []
        for sig,val in pattern.items():
            center,basis = charts[sig]
            rem, code = basis.decompose(val ^ center)
            if rem:
                raise AssertionError("incomplete value basis")
            row.extend(v if (code >> j) & 1 else -v for j,v in enumerate(blocks[sig]))
        clauses.append(row)
    true = _horn(clauses)
    if true is None:
        return dict(status="zero")
    for sig,block in blocks.items():
        if not sig & (1 << len(spaces)):
            continue
        value = 0
        if sig in charts:
            center,basis = charts[sig]
            code = sum(1 << j for j,v in enumerate(block) if v not in true)
            value = center ^ _combine(basis.axes, code)
        for j,v in enumerate(block):
            if not _insert(axes[v-1], (value >> j) & 1, eq):
                raise AssertionError("inconsistent chart lift")
    word = _lift(eq)
    ids = tuple(v for j,v in enumerate(used) if word & (1 << j))
    chosen = set(ids)
    if not all(any((abs(x) in chosen) == (x>0) for x in row) for row in rows):
        raise AssertionError("invalid original source witness")
    return dict(status="nonzero", true_ids=ids)


def solve_sparse(n, clauses, point, k):
    source = recover(n, clauses, point, k)
    return dict(status="off_image") if source is None else solve_source_sparse(*source)
