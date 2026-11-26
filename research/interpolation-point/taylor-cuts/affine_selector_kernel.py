"""Recognize explicit at-most-one signed affine forms and split their fibers."""
from itertools import combinations
from affine_cover_solver import insert, solve


def _rows(n, flat):
    rows = tuple(flat)
    for mask, bit in rows:
        if not isinstance(mask, int) or mask < 0 or mask.bit_length() > n or bit not in (0,1):
            raise ValueError("invalid affine equation")
    return rows


def find_selector(n, flats):
    """Return verified (mask,offset) forms, or (). Try one extraneous neighbor."""
    if not isinstance(n,int) or n < 0:
        raise ValueError("invalid dimension")
    graph, planes = {}, {}
    for flat in flats:
        basis = {}
        rows = _rows(n, flat)
        if not all(insert(mask, bit, basis) for mask,bit in rows) or len(basis) != 2:
            continue
        (p,a),(q,b) = basis.values()
        forms = ((p,a^1),(q,b^1),(p^q,a^b^1))
        plane = tuple(sorted(mask for mask,_ in forms))
        for v in forms:
            planes.setdefault(v,set()).add(plane)
            graph.setdefault(v,set()).update(w for w in forms if w != v)
    active = {v for v in graph if len(planes[v]) >= 2}
    best = ()
    for v in sorted(active):
        neighbors = sorted(graph[v] & active)
        for omit in [None, *neighbors]:
            candidate = tuple(sorted([v, *(w for w in neighbors if w != omit)]))
            if len(candidate) > max(2,len(best)) and all(
                    b in graph[a] for a,b in combinations(candidate,2)):
                best = candidate
    return best


def selector_slices(n, forms, seed=()):
    """Yield feasible, disjoint equation bases for zero/unit form words.

    Coverage requires a certified at-most-one property. Each form equals
    parity(mask & x) XOR offset. The empty form list gives one fiber.
    """
    if not isinstance(n,int) or n < 0:
        raise ValueError("invalid dimension")
    forms = _rows(n, forms)
    base = {}
    if not all(insert(mask, bit, base) for mask, bit in _rows(n,seed)):
        return
    for selected in range(-1,len(forms)):
        basis = base.copy()
        if all(insert(mask, offset ^ (i == selected), basis)
               for i,(mask,offset) in enumerate(forms)):
            yield tuple(basis.values())


def solve_selector(n, flats, seed=(), *, leaf=solve):
    """Return an original-coordinate witness or None, with exact slice fallback."""
    flats = tuple(_rows(n,flat) for flat in flats)
    forms = find_selector(n,flats)
    for equations in selector_slices(n,forms,seed):
        witness = leaf(n,flats,equations)
        if witness is not None:
            return witness
    return None
