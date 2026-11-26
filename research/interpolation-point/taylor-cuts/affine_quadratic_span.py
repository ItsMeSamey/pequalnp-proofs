"""Exact counting by quadratic span for Boolean forbidden affine flats."""
from itertools import combinations
from affine_cover_solver import insert


class IncompleteQuadraticSpan(ValueError):
    """The quadratic projection does not have full column rank."""


def _normalize(n, flats):
    if not isinstance(n, int) or n < 0:
        raise ValueError("dimension must be a nonnegative integer")
    output = []
    for flat in flats:
        basis = {}
        consistent = True
        for mask, bit in flat:
            if not isinstance(mask, int) or not 0 <= mask < 1 << n or bit not in (0, 1):
                raise ValueError("invalid affine equation")
            consistent &= insert(mask, bit, basis)
        if consistent:
            if len(basis) > 2:
                raise ValueError("rank exceeds two")
            output.append(tuple(basis.values()))
    return output


def _pivots(n, flats):
    pairs = list(combinations(range(n), 2))
    pivots = {}
    for flat in flats:
        if len(flat) < 2:
            continue
        (a,u),(b,v) = flat
        u ^= 1
        v ^= 1
        linear = (a & b) ^ (a if v else 0) ^ (b if u else 0)
        row = (linear << 1) | (u & v)
        for col,(i,j) in enumerate(pairs,n+1):
            if ((a>>i & b>>j) ^ (a>>j & b>>i)) & 1:
                row |= 1 << col
        while row.bit_length() > n+1:
            k = row.bit_length()-1
            if k not in pivots:
                pivots[k] = row
                break
            row ^= pivots[k]
    return pairs,pivots


def _missing(n,pairs,pivots):
    return [p for j,p in enumerate(pairs,n+1) if j not in pivots]


def _cover(edges):
    # Endpoints of a maximal matching form a two-approximation.
    chosen = set()
    for i,j in edges:
        if i not in chosen and j not in chosen:
            chosen.update((i,j))
    return tuple(sorted(chosen))


def quadratic_cover(n,flats):
    """Return a coordinate cover of the nonpivot quadratic columns."""
    pairs,pivots = _pivots(n,_normalize(n,flats))
    return _cover(_missing(n,pairs,pivots))


def _eigenspace(space,matrix,bit):
    pivots = {}
    kernel = []
    for vector in space:
        image = vector if bit else 0
        for i,poly in enumerate(matrix):
            image ^= ((vector & poly).bit_count() & 1) << i
        preimage = vector
        while image:
            k = image.bit_length()-1
            if k not in pivots:
                pivots[k] = image,preimage
                break
            v,w = pivots[k]
            image ^= v
            preimage ^= w
        else:
            kernel.append(preimage)
    return kernel


def _full(n,flats):
    if () in flats:
        return 0,None
    pairs,pivots = _pivots(n,flats)
    if len(pivots) != len(pairs):
        raise IncompleteQuadraticSpan("missing independent quadratic columns")
    matrices = []
    for i in range(n):
        row = [0]*(n+1)
        row[0] = row[i+1] = 1 << (i+1)
        matrices.append(row)
    for col,(i,j) in enumerate(pairs,n+1):
        rest = pivots[col] ^ (1 << col)
        while rest.bit_length() > n+1:
            rest ^= pivots[rest.bit_length()-1]
        pivots[col] = (1 << col) | rest
        matrices[i][j+1] = matrices[j][i+1] = rest
    layers = [(0,[1<<k for k in range(n+1)])]
    for i,matrix in enumerate(matrices):
        next_layer = []
        for prefix,space in layers:
            for bit in (0,1):
                child = _eigenspace(space,matrix,bit)
                if child:
                    next_layer.append((prefix | (bit<<i),child))
        layers = next_layer
    answers = [x for x,_ in layers if all(
        any((x&a).bit_count()%2 != b for a,b in flat) for flat in flats)]
    return len(answers), (answers[0] if answers else None)


def solve_quadratic_full(n,flats):
    """Return (count,witness or None); raise IncompleteQuadraticSpan on rank defect."""
    return _full(n,_normalize(n,flats))


def solve_quadratic(n,flats,cover=None):
    """Return (count,witness) by pinning a cover of the nonpivot pairs."""
    flats = _normalize(n,flats)
    if () in flats:
        return 0,None
    pairs,pivots = _pivots(n,flats)
    missing = _missing(n,pairs,pivots)
    fixed = _cover(missing) if cover is None else tuple(cover)
    if any(not isinstance(i,int) or not 0<=i<n for i in fixed) or len(set(fixed))!=len(fixed):
        raise ValueError("invalid cover coordinates")
    chosen = set(fixed)
    if any(i not in chosen and j not in chosen for i,j in missing):
        raise ValueError("supplied coordinates do not cover the nonpivot pairs")
    if not fixed:
        return _full(n,flats)
    free = [i for i in range(n) if i not in chosen]
    projected = [[(sum(((a>>i)&1)<<j for j,i in enumerate(free)),a,b)
                  for a,b in flat] for flat in flats]
    total,witness = 0,None
    for pattern in range(1<<len(fixed)):
        pinned = sum(((pattern>>j)&1)<<i for j,i in enumerate(fixed))
        residual = [[(small,b^((a&pinned).bit_count()%2)) for small,a,b in flat]
                    for flat in projected]
        count,first = solve_quadratic_full(len(free),residual)
        total += count
        if witness is None and first is not None:
            witness = pinned | sum(((first>>j)&1)<<i for j,i in enumerate(free))
    return total,witness
