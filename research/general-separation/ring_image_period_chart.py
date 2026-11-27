"""Projected forbidden tuples on simultaneous essential affine coordinates."""
from read_two_ring_image import recover
from ring_image_affine_hull_sparse import _closure, _combine, _flat
from ring_image_beta_chart import _nest_order, _nested_sat
from ring_image_common_basis import common_basis
from ring_image_coordinate_2sat import _insert, _lift
from ring_image_group_horn_strict import solve_tuples


def essential_normals(words, dimension):
    """Basis of the orthogonal complement of the full translation stabilizer."""
    if not words:
        return []
    anchor = min(words)
    periods = set()
    for word in words:
        v = word ^ anchor
        if all((w ^ v) in words for w in words):
            periods.add(v)
    normals, flat = _flat(periods, dimension)
    if not flat:
        raise AssertionError("translation periods must form a subspace")
    return [v for v,_ in normals]


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
    clauses = []
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
        clauses.extend(frozenset(-j if w >> t & 1 else j for t,j in enumerate(ids))
                       for w in masks)
    order = _nest_order(clauses)
    if order is not None:
        true = _nested_sat(clauses,order)
        if true is None:
            return dict(status="zero")
    else:
        horn = solve_tuples(tuples)
        if horn["status"] == "unknown":
            return dict(status="unknown",reason="not_beta_or_chart_horn")
        if horn["status"] == "zero":
            return dict(status="zero")
        true = {v for v,b in horn["assignment"].items() if b}
    for j,(a,t) in enumerate(zip(axes,signatures),1):
        if t >> len(spaces) & 1 and not _insert(a,int(j in true),eq):
            raise AssertionError("inconsistent chart lift")
    word = _lift(eq)
    ids = tuple(v for i,v in enumerate(used) if word >> i & 1)
    selected = set(ids)
    if not all(any((abs(l) in selected) == (l>0) for l in row) for row in rows):
        raise AssertionError("invalid lifted source witness")
    return dict(status="nonzero",true_ids=ids)


def solve_sparse(n, clauses, point, k):
    source = recover(n, clauses, point, k)
    return dict(status="off_image") if source is None else solve_source_sparse(*source)
