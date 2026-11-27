"""Search origins when one saturated essential scope spans all active normals."""
from read_two_ring_image import recover
from ring_image_affine_hull_sparse import _closure, _combine
from ring_image_common_basis import span
from ring_image_coordinate_2sat import _insert, _lift
from ring_image_origin_horn import solve_source_sparse as fixed_origin
from ring_image_period_chart import essential_normals


def solve_source_sparse(arity, signed_clauses):
    rows = tuple(tuple(row) for row in signed_clauses)
    if type(arity) is not int or arity < 0 or any(
            type(l) is not int or not 1 <= abs(l) <= arity for row in rows for l in row):
        raise ValueError("invalid arity or signed literal")
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
    saturated = []
    all_normals = []
    for projection,words in projected:
        local = essential_normals(words,len(projection.axes))
        normals = [_combine(projection.axes,a) for a in local]
        patterns = {sum(((a & t).bit_count() % 2) << j for j,a in enumerate(local)) for t in words}
        if len(patterns) > len(normals)+1:
            return dict(status="unknown", reason="too_many_forbidden_patterns")
        all_normals.extend(normals)
        if len(patterns) == len(normals)+1:
            saturated.append((normals,patterns))
    rank = len(span(all_normals).axes)
    for normals, patterns in saturated:
        if len(normals) != rank:
            continue
        for pattern in sorted(patterns):
            lifted = eq.copy()
            for j,a in enumerate(normals):
                if not _insert(a,pattern >> j & 1,lifted):
                    raise AssertionError("unreachable essential tuple")
            p = _lift(lifted)
            ids = tuple(v for j,v in enumerate(used) if p >> j & 1)
            result = fixed_origin(arity,rows,origin_true_ids=ids)
            if result["status"] != "unknown":
                return result
        return dict(status="unknown",reason="no_adapted_tuple_horn_origin")
    return fixed_origin(arity,rows)


def solve_sparse(n, clauses, point, k):
    source = recover(n, clauses, point, k)
    return dict(status="off_image") if source is None else solve_source_sparse(*source)
