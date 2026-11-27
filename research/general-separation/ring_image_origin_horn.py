"""Search all adapted bases for point-centered Horn *full tuple* clauses."""
from read_two_ring_image import recover
from ring_image_period_chart import essential_normals
from ring_image_affine_hull_sparse import _closure, _combine
from ring_image_common_basis import common_basis, span
from ring_image_coordinate_2sat import _insert, _lift


def solve_source_sparse(arity, signed_clauses, *, origin_true_ids=None):
    rows = tuple(tuple(row) for row in signed_clauses)
    if type(arity) is not int or arity < 0 or any(
            type(l) is not int or not 1 <= abs(l) <= arity for row in rows for l in row):
        raise ValueError("invalid arity or signed literal")
    origin = None if origin_true_ids is None else set(origin_true_ids)
    if origin is not None and any(type(v) is not int or not 1 <= v <= arity for v in origin):
        raise ValueError("invalid origin ID")
    used = sorted({abs(l) for row in rows for l in row})
    idx = {v:i for i,v in enumerate(used)}
    groups = {}
    for row in rows:
        lits = set(row)
        if any(-l in lits for l in lits):
            continue
        names = sorted(map(abs,lits))
        scope = tuple(idx[v] for v in names)
        groups.setdefault(scope,set()).add(sum(1 << j for j,v in enumerate(names) if -v in lits))
    eq, projected = _closure(groups)
    if eq is None:
        return dict(status="zero")
    p = _lift(eq) if origin is None else sum(1 << idx[v] for v in origin if v in idx)
    if any((p & a).bit_count() % 2 != b for a,b in eq.values()):
        return dict(status="unknown", reason="origin_outside_hull")
    spaces = []
    records = []
    for projection, words in projected:
        local = essential_normals(words,len(projection.axes))
        normals = [_combine(projection.axes,v) for v in local]
        widx = len(spaces)
        spaces.append(normals)
        normal_span = span(normals)
        pbits = sum(((a & p).bit_count() % 2) << j for j,a in enumerate(normals))
        offsets = {pbits ^ sum(((a & t).bit_count() % 2) << j for j,a in enumerate(local))
                   for t in words}
        for delta in offsets:
            if delta:
                k = (delta & -delta).bit_length()-1
                kernel = [a ^ (normals[k] if delta >> j & 1 else 0)
                          for j,a in enumerate(normals) if j != k]
                spaces.append(kernel)
            records.append((widx,normal_span,delta))
    free_idx = len(spaces)
    spaces.append([1 << i for i in range(len(used)) if i not in eq])
    chart = common_basis(len(used),spaces)
    if chart is None:
        return dict(status="unknown",reason="no_origin_tuple_chart")
    axes, signatures = chart
    rules = []
    for widx, normal_span, delta in records:
        body = []
        head = None
        for j,(a,sig) in enumerate(zip(axes,signatures)):
            if not sig >> widx & 1:
                continue
            code = normal_span.decompose(a)[1]
            if (code & delta).bit_count() % 2:
                if head is not None:
                    raise AssertionError("incompatible tuple kernel")
                head = j
            else:
                body.append(j)
        rules.append((body,head))
    true = set()
    while True:
        before = len(true)
        for body,head in rules:
            if all(j in true for j in body):
                if head is None:
                    return dict(status="zero")
                true.add(head)
        if len(true) == before:
            break
    for j,(a,sig) in enumerate(zip(axes,signatures)):
        if sig >> free_idx & 1:
            bit = 1 ^ int(j in true) ^ ((a & p).bit_count() % 2)
            if not _insert(a,bit,eq):
                raise AssertionError("inconsistent lift")
    word = _lift(eq)
    ids = tuple(v for i,v in enumerate(used) if word >> i & 1)
    selected = set(ids)
    if not all(any((abs(l) in selected) == (l>0) for l in row) for row in rows):
        raise AssertionError("invalid source witness")
    return dict(status="nonzero",true_ids=ids)


def solve_sparse(n, clauses, point, k, *, origin_true_ids=None):
    source = recover(n, clauses, point, k)
    if source is None:
        return dict(status="off_image")
    return solve_source_sparse(*source, origin_true_ids=origin_true_ids)
