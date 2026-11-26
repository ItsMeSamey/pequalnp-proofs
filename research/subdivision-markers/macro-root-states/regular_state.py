"""One mixed boundary state as a homogeneous pair on a target-dependent host."""
from macro import functional, image, solve
from three import dual_representation


def homogeneous_query(cols, port, coord, f):
    """Return H, cycle labels, cocycle labels, score target and score bit width."""
    assert coord and f and not (coord & f).bit_count() % 2
    u = image(port, coord)
    pivot = u & -u
    H = tuple(v ^ u if v & pivot else v for v in cols)
    primal = tuple(int(bool(v & pivot)) for v in cols)
    dual = [0] * len(cols)
    target = 1
    omitted = (coord & -coord).bit_length() - 1
    next_bit = 1
    for j, v in enumerate(port):
        if j == omitted:
            continue
        coeff = solve(cols, v)
        assert coeff is not None
        for i in range(len(cols)):
            if coeff >> i & 1:
                dual[i] |= 1 << next_bit
        target |= ((f >> j) & 1) << next_bit
        next_bit += 1
    return H, primal, tuple(dual), target, len(port)


def dual_query(cols, port, coord, f):
    dual = dual_representation(tuple(cols) + tuple(port))
    n = len(cols)
    return dual[:n], dual[n:], f, coord


def lift(cols, port, coord, f, c, dual_orientation=False):
    u = image(port, coord)
    if dual_orientation:
        available = [i for i in range(len(cols)) if not c >> i & 1]
        add = solve(tuple(cols[i] for i in available), u)
        assert add is not None
        c = sum(1 << i for j, i in enumerate(available) if add >> j & 1)
    chosen = tuple(v for i, v in enumerate(cols) if c >> i & 1)
    assert image(cols, c) == u and functional(tuple(port) + chosen, f) is not None
    return c


def solve_regular_state(local, port, coord, f, oracle):
    """Oracle returns 'unsupported', None, or a (cycle,cocycle) pair on H."""
    ids, cols = zip(*local)
    for reverse, args in [(False, (cols, port, coord, f)), (True, dual_query(cols, port, coord, f))]:
        H, L, M, p, t = homogeneous_query(*args)
        pair = oracle(H, L, M, p, t)
        if pair == "unsupported":
            continue
        if pair is None:
            return None
        c,d = pair
        assert not c & d and not image(H,c) and image(L,c)^image(M,d)==p
        assert functional(H,d) is not None
        mask = lift(cols,port,coord,f,c,reverse)
        return sum(1 << idx for j,idx in enumerate(ids) if mask >> j & 1)
    return "unsupported"
