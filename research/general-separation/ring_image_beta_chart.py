"""Beta-acyclic transformed CNF after sparse affine-hull closure."""
from read_two_ring_image import recover
from ring_image_affine_hull_sparse import _closure, _combine, _flat
from ring_image_common_basis import common_basis, span
from ring_image_coordinate_2sat import _insert, _lift


def _nest_order(rows):
    scopes = {frozenset(map(abs,row)) for row in rows}
    live = set().union(*scopes) if scopes else set()
    order = []
    while live:
        for v in sorted(live):
            incident = sorted((s for s in scopes if v in s), key=len)
            if all(a <= b for a,b in zip(incident, incident[1:])):
                break
        else:
            return None
        live.remove(v)
        order.append(v)
        scopes = {s - {v} for s in scopes}
    return order


def _nested_sat(rows, order):
    deleted = []
    rows = set(rows)
    for v in order:
        pos = [r for r in rows if v in r]
        neg = [r for r in rows if -v in r]
        deleted.append((v,pos,neg))
        rows.difference_update(pos, neg)
        for p in pos:
            for q in neg:
                resolvent = (p - {v}) | (q - {-v})
                if all(-l not in resolvent for l in resolvent):
                    rows.add(resolvent)
    if frozenset() in rows:
        return None
    true = set()
    def forced(row,v):
        return all((abs(l) in true) != (l>0) for l in row if abs(l) != v)
    for v,pos,neg in reversed(deleted):
        if any(forced(r,v) for r in pos):
            if any(forced(r,v) for r in neg):
                raise AssertionError("inconsistent resolution lift")
            true.add(v)
    return true


def solve_source_sparse(arity, signed_clauses):
    rows = tuple(tuple(row) for row in signed_clauses)
    if type(arity) is not int or arity < 0 or any(
            type(l) is not int or not 1 <= abs(l) <= arity for row in rows for l in row):
        raise ValueError("invalid arity or signed source literal")
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
    normals = []
    for projection, words in projected:
        local, flat = _flat(words, len(projection.axes))
        if not flat:
            return dict(status="unknown", reason="nonflat")
        normals.append([(_combine(projection.axes,v), b) for v,b in local])
    # Require a coordinate basis of the free subspace; all normals lie in it.
    free = [1 << i for i in range(len(used)) if i not in eq]
    chart = common_basis(len(used), [[a for a,_ in s] for s in normals] + [free])
    if chart is None:
        return dict(status="unknown", reason="incompatible_spaces")
    axes, signatures = chart
    clauses = []
    for i, tests in enumerate(normals):
        space = span(a for a,_ in tests)
        offset = sum(b << j for j,(_,b) in enumerate(tests))
        clause = []
        for j,(a,t) in enumerate(zip(axes,signatures),1):
            if t >> i & 1:
                code = space.decompose(a)[1]
                clause.append(-j if (code & offset).bit_count() & 1 else j)
        clauses.append(frozenset(clause))
    order = _nest_order(clauses)
    if order is None:
        return dict(status="unknown", reason="not_beta_acyclic")
    true = _nested_sat(clauses, order)
    if true is None:
        return dict(status="zero")
    for j,(a,t) in enumerate(zip(axes,signatures),1):
        if t >> len(normals) & 1 and not _insert(a,int(j in true),eq):
            raise AssertionError("inconsistent quotient lift")
    word = _lift(eq)
    ids = tuple(v for i,v in enumerate(used) if word >> i & 1)
    selected = set(ids)
    if not all(any((abs(l) in selected) == (l > 0) for l in row) for row in rows):
        raise AssertionError("invalid sparse source witness")
    return dict(status="nonzero", true_ids=ids)


def solve_sparse(n, clauses, point, k):
    source = recover(n, clauses, point, k)
    return dict(status="off_image") if source is None else solve_source_sparse(*source)
