"""One-tag indexed alternating search with rank-four physical signature pruning."""
from itertools import combinations
from component_nullity import bits, dependencies
from thick_tag_solver import basis, combine, reduce_vector
from three_name_adapter import three_name


def dot(x, y):
    return (x & y).bit_count() & 1


def signatures(words, n):
    return [sum(((word >> i) & 1) << j for j, word in enumerate(words)) for i in range(n)]


def _rank_two(private, tag, omega, safe):
    """safe spans all feasible cycles in this restricted physical ground."""
    gram = [sum(int(bool(omega(x, y))) << j for j, y in enumerate(safe)) for x in safe]
    match = next(((i, j) for i, row in enumerate(gram) for j in bits(row)), None)
    if match is None:
        return None
    i, j = match
    if len(basis(gram)[1]) > 2:
        raise ValueError("rank-two oracle called on larger restriction")
    pivot, _ = basis(safe)
    kernel = dependencies(private)
    axis = [0, 0, 0]
    for k, cycle in enumerate(kernel):
        coord = reduce_vector(cycle, pivot)[1]
        for a, value in enumerate((combine(tag, cycle), dot(gram[i], coord), dot(gram[j], coord))):
            axis[a] |= value << k
    if len(basis(axis)[1]) < 3:
        if axis[0] or len(basis(axis[1:])[1]) < 2:
            return None
        keep = list(range(len(private)))
    else:
        # Coordinates in the named basis, then units extending it in R*.
        axes = axis + [1 << k for k in range(len(kernel))]
        named_basis, _ = basis(axes)
        cols = [reduce_vector(e, named_basis)[1] for e in signatures(kernel, len(private))]
        removed = three_name([c >> 3 for c in cols], [c & 7 for c in cols], 1)
        if removed is None:
            return None
        removed = set(removed)
        keep = [i for i in range(len(private)) if i not in removed]
    words = [sum(1 << keep[j] for j in bits(w)) for w in dependencies([private[i] for i in keep])]
    if any(combine(tag, w) for w in words):
        raise ArithmeticError("dual trace failed original tag check")
    return next((pair for pair in combinations(words, 2) if omega(*pair)), None)


def _linear(equations, n):
    """Return an origin and homogeneous directions, or None."""
    cols = [sum(((row >> i) & 1) << j for j, (row, _) in enumerate(equations)) for i in range(n)]
    target = sum(v << j for j, (_, v) in enumerate(equations))
    table, ids = basis(cols)
    rem, coeff = reduce_vector(target, table)
    if rem:
        return None
    return sum(1 << ids[j] for j in bits(coeff)), dependencies(cols)


def solve(private, tag, omega, L=None, limit_bits=0):
    """Return status and a pair of original-index masks on YES.

    A supplied independent L must contain every compatible private cycle.
    Its containment in the private kernel is verified; coverage is a caller
    promise. The default uses the kernel of private columns augmented by tag.
    UNKNOWN indicates rank above four or a consistent residual linear system
    with more than limit_bits free bits. omega must be alternating bilinear.
    """
    private, tag = list(private), list(tag)
    n = len(private)
    if (len(tag) != n or any(type(v) is not int or v < 0 for v in private)
            or any(t not in (0, 1) for t in tag) or type(limit_bits) is not int or limit_bits < 0):
        raise ValueError("invalid one-tag input")
    safe = list(L) if L is not None else dependencies([(v << 1) | t for v, t in zip(private, tag)])
    if (any(type(w) is not int or w < 0 or w >> n or combine(private, w) for w in safe)
            or dependencies(safe)):
        raise ValueError("L must be an independent private-kernel basis")
    gram = [sum(int(bool(omega(x, y))) << j for j, y in enumerate(safe)) for x in safe]
    _, selected = basis(gram)
    rank = len(selected)
    if rank <= 2:
        pair = _rank_two(private, tag, omega, safe)
        return ("YES", pair) if pair else ("NO", None)
    if rank != 4:
        return "UNKNOWN", None
    m = len(safe)
    forms = [gram[i] for i in selected]
    extra = [1 << k for k in range(m)]
    dual, chosen = basis(forms + extra)
    frame = [(forms + extra)[i] for i in chosen]
    sig = [reduce_vector(v, dual)[1] for v in signatures(safe, n)]
    groups = {}
    for i, s in enumerate(sig):
        groups.setdefault(s >> 4, {}).setdefault(s & 15, i)

    def deletion(removed):
        keep = [i for i in range(n) if i not in removed]
        # Intersect L with the coordinate-zero constraints, then reindex.
        cuts = [sum(((w >> i) & 1) << j for j, i in enumerate(removed)) for w in safe]
        coeffs = dependencies(cuts)
        restrict = lambda w: sum(((w >> i) & 1) << j for j, i in enumerate(keep))
        lift = lambda w: sum(1 << keep[j] for j in bits(w))
        local = [restrict(combine(safe, c)) for c in coeffs]
        pair = _rank_two([private[i] for i in keep], [tag[i] for i in keep],
                         lambda x, y: omega(lift(x), lift(y)), local)
        return tuple(lift(w) for w in pair) if pair else None

    for f, i in groups.get(0, {}).items():
        if f and (pair := deletion([i])):
            return "YES", pair
    for q, fs in groups.items():
        if q:
            for i, j in combinations(fs.values(), 2):
                if pair := deletion([i, j]):
                    return "YES", pair

    primal = signatures(frame, m)
    image_basis, image_ids = basis(primal)
    def lift_image(v):
        rem, coeff = reduce_vector(v, image_basis)
        if rem:
            raise ArithmeticError("incomplete dual frame")
        return combine(safe, sum(1 << image_ids[j] for j in bits(coeff)))

    unit = [lift_image(1 << i) for i in range(m)]
    s = m - 4
    unknown = False
    for a, b in combinations(range(1, 16), 2):
        if b > (a ^ b) or not omega(combine(unit, a), combine(unit, b)):
            continue
        offset = lambda f: dot(f, a) | (dot(f, b) << 1)
        if any(f and not offset(f) for f in groups.get(0, {})):
            continue
        equations, bans = [], []
        for q, fs in groups.items():
            if not q:
                continue
            counts = [0]*4
            for f in fs:
                counts[offset(f)] += 1
            allowed = [v for v, count in enumerate(counts) if count <= 1]
            if not allowed:
                break
            bans.append((q, set(allowed)))
            if len(allowed) <= 2:
                for h in (1, 2, 3):
                    values = {dot(h, v) for v in allowed}
                    if len(values) == 1:
                        row = (q if h & 1 else 0) ^ ((q << s) if h & 2 else 0)
                        equations.append((row, values.pop()))
        else:
            result = _linear(equations, 2*s)
            if result is None:
                continue
            origin, free = result
            if len(free) > limit_bits:
                unknown = True
                continue
            for choices in range(1 << len(free)):
                z = origin ^ combine(free, choices)
                zx, zy = z & ((1 << s)-1), z >> s
                if any((dot(q, zx) | (dot(q, zy) << 1)) not in ok for q, ok in bans):
                    continue
                x = combine(unit, a | (zx << 4))
                y = combine(unit, b | (zy << 4))
                ids = list(bits(x | y))
                words = dependencies([private[i] for i in ids])
                if all(not combine([tag[i] for i in ids], w) for w in words):
                    if not omega(x, y):
                        raise ArithmeticError("incorrect symplectic lift")
                    return "YES", (x, y)
    return ("UNKNOWN" if unknown else "NO"), None


def check_small():
    from random import Random
    from pathlib import Path
    from runpy import run_path

    rng = Random(223)
    for trial in range(60):
        n = rng.randrange(3, 9)
        private = [rng.randrange(4) for _ in range(n)]
        tag = [rng.randrange(2) for _ in range(n)]
        safe = dependencies([(v << 1) | t for v, t in zip(private, tag)])
        h = [rng.randrange(1 << n) for _ in range(4)]
        def omega(x, y):
            return ((dot(h[0], x)*dot(h[1], y)) ^ (dot(h[0], y)*dot(h[1], x))
                    ^ (dot(h[2], x)*dot(h[3], y)) ^ (dot(h[2], y)*dot(h[3], x)))
        reference = False
        for chart in range(4):
            active = sum(1 << i for i, (v, t) in enumerate(zip(private, tag)) if dot(chart, v) == t)
            words = [w for w in range(1 << n) if not w & ~active and not combine(private, w)]
            reference |= any(omega(x, y) for x, y in combinations(words, 2))
        status, pair = solve(private, tag, omega, safe if trial % 2 else None, 2*n)
        assert status == ("YES" if reference else "NO")
        if pair:
            x, y = pair
            assert not combine(private, x) and not combine(private, y) and omega(x, y)
            assert any(all(dot(g, private[i]) == tag[i] for i in bits(x | y)) for g in range(4))
    fixture = run_path(str(Path(__file__).resolve().parents[1] / "np-sum-independent/k6_physical_check.py"))
    private = signatures(fixture["K"], 15)
    tag = [(fixture["tag"] >> j) & 1 for j in range(15)]
    pivots, _ = basis(fixture["L"])
    def obstruction(x, y):
        x, y = (reduce_vector(w, pivots)[1] for w in (x, y))
        return dot(63, fixture["wedge"](x, y))
    assert solve(private, tag, obstruction, fixture["L"]) == ("NO", None)


if __name__ == "__main__":
    check_small()
    print("60 direct chart/word comparisons and the K6 rank-four obstruction passed")
