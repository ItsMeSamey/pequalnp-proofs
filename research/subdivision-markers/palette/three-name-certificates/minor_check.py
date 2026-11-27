"""Verify labelled excluded-minor witnesses and match fixed small targets."""
from itertools import combinations, permutations


def _reduce(x, basis):
    for bit in sorted(basis, reverse=True):
        if x & (1 << bit):
            x ^= basis[bit]
    return x


def _basis(vectors):
    basis = {}
    for x in vectors:
        x = _reduce(x, basis)
        if x:
            basis[x.bit_length()-1] = x
    return basis


def _dual(columns):
    # Dependencies indexed by the nonbasis labels give a nullspace basis.
    pivots = {}
    rows = []
    for i, x in enumerate(columns):
        mask = 1 << i
        while x and x.bit_length() in pivots:
            v, tag = pivots[x.bit_length()]
            x ^= v
            mask ^= tag
        if x:
            pivots[x.bit_length()] = x, mask
        else:
            rows.append(mask)
    return tuple(sum(((row >> i) & 1) << j for j,row in enumerate(rows))
                 for i in range(len(columns)))


_FANO = tuple(range(1,8))
_K5 = tuple((1<<u)|(1<<v) for u,v in combinations(range(5),2))
_K33 = tuple((1<<u)|(1<<v) for u in range(3) for v in range(3,6))
_TARGETS = {"F7": _FANO, "F7*": _dual(_FANO),
            "M*(K5)": _dual(_K5), "M*(K3,3)": _dual(_K33)}


def verify_minor(columns, retain, contract, delete, target):
    """retain[i] gives original position of target label i. Graph edges use
    lexicographic order, K3,3 parts 0..2 and 3..5. Fano columns are 1..7.
    """
    if not isinstance(target,str) or target not in _TARGETS or isinstance(retain,(set,frozenset,dict)):
        return False
    try:
        cols = tuple(columns)
        r,c,d = tuple(retain),tuple(contract),tuple(delete)
    except TypeError:
        return False
    pos = r+c+d
    if any(type(x) is not int or x<0 for x in cols+pos):
        return False
    if len(pos)!=len(cols) or set(pos)!=set(range(len(cols))) or len(r)!=len(_TARGETS[target]):
        return False
    base = _basis(cols[i] for i in c)
    quotient = [_reduce(cols[i],base) for i in r]
    # A binary dependence is precisely a subset with zero XOR. Equality
    # of the two labelled kernels checks every dependence at once.
    for mask in range(1,1<<len(r)):
        actual = expected = 0
        for i,v in enumerate(quotient):
            if mask >> i & 1:
                actual ^= v
                expected ^= _TARGETS[target][i]
        if bool(actual)!=bool(expected):
            return False
    return True


def _span(vectors):
    values = [0]
    for v in vectors:
        values += [x^v for x in values]
    return values


def match_excluded_minor(columns):
    """Return target name and ordered original positions for a whole candidate."""
    cols = tuple(columns)
    if any(type(x) is not int or x<0 for x in cols):
        return None
    positions = {x:i for i,x in enumerate(cols)}
    if len(positions)!=len(cols) or 0 in positions:
        return None
    rank = len(_basis(cols))
    for name,target in _TARGETS.items():
        if len(cols)!=len(target) or rank!=len(_basis(target)):
            continue
        basis = []
        for x in target:
            if x not in _span(basis):
                basis.append(x)
        lookup = {x:i for i,x in enumerate(_span(basis))}
        masks = [lookup[x] for x in target]
        for selected in combinations(cols,rank):
            if len(_basis(selected))!=rank:
                continue
            for perm in permutations(selected):
                images = _span(perm)
                if all(images[m] in positions for m in masks):
                    return name,tuple(positions[images[m]] for m in masks)
    return None
