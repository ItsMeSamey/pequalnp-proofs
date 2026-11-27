"""First-version coordinate chart solver on compressed, binary-named variables."""
from read_two_ring_image import recover
from ring_image_coordinate_2sat import solve_source as _solve_compact


def solve_source_sparse(arity, signed_clauses):
    if type(arity) is not int or arity < 0:
        raise ValueError("invalid arity")
    source = tuple(tuple(row) for row in signed_clauses)
    if any(type(lit) is not int or not 1 <= abs(lit) <= arity
           for row in source for lit in row):
        raise ValueError("invalid signed literal")
    used = sorted({abs(lit) for row in source for lit in row})
    ranks = {v:i for i,v in enumerate(used, 1)}
    compact = [[ranks[abs(lit)] * (1 if lit > 0 else -1) for lit in row] for row in source]
    result = _solve_compact(len(used), compact)
    if result["status"] != "nonzero":
        return result
    true_ids = tuple(v for v,b in zip(used,result["assignment"]) if b)
    selected = set(true_ids)
    if not all(any((abs(lit) in selected) == (lit > 0) for lit in row) for row in source):
        raise AssertionError("invalid sparse witness")
    return dict(status="nonzero", true_ids=true_ids)


def solve_sparse(n, clauses, point, k):
    source = recover(n, clauses, point, k)
    return dict(status="off_image") if source is None else solve_source_sparse(*source)
