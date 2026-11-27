"""Automatic central torso extraction by pinned represented matroid intersection."""
from collections import deque
from itertools import combinations
from central_uplift import combine, dependencies, expand_witness, mul, rank, reduce_central, three_connected
from component_nullity import bits


def _pinned(cols, s, t):
    """Return a minimizer of lambda among partitions separating s from t."""
    seeds = ([cols[i] for i in s], [cols[i] for i in t])
    base = [rank(seed) for seed in seeds]
    ground = set(range(len(cols))) - set(s) - set(t)
    chosen = set()

    def good(k, ids):
        return rank(seeds[k] + [cols[i] for i in ids]) == base[k] + len(ids)

    while True:
        outside = ground - chosen
        pred = {i: None for i in outside if good(0, chosen | {i})}
        queue = deque(pred)
        end = None
        while queue and end is None:
            i = queue.popleft()
            if i in chosen:
                adjacent = [j for j in outside if good(0, (chosen - {i}) | {j})]
            else:
                if good(1, chosen | {i}):
                    end = i
                    break
                adjacent = [j for j in chosen if good(1, (chosen - {j}) | {i})]
            for j in adjacent:
                if j not in pred:
                    pred[j] = i
                    queue.append(j)
        if end is None:
            # Reachable elements are on the second side of the min-max partition.
            side = set(s) | (ground - pred.keys())
            other = set(range(len(cols))) - side
            if rank([cols[i] for i in side]) + rank([cols[i] for i in other]) != sum(base) + len(chosen):
                raise ArithmeticError("intersection partition failed rank certificate")
            return side
        while end is not None:
            chosen.symmetric_difference_update([end])
            end = pred[end]


def find_split(cols):
    """Find a proper 2-separation of a connected represented matroid."""
    ids = set(range(len(cols)))
    full = rank(cols)
    for s in combinations(sorted(ids), 2):
        for t in combinations(sorted(ids-set(s)), 2):
            if s > t:
                continue
            side = _pinned(cols, s, t)
            other = ids - side
            lam = rank([cols[i] for i in side]) + rank([cols[i] for i in other]) - full
            if lam == 0:
                raise ValueError("disconnected torso")
            if lam == 1:
                return side
    return None


def _marker(cols, side):
    """Track left-side contributions during elimination to recover an interface."""
    pivots = {}
    order = sorted(side) + sorted(set(range(len(cols))) - side)
    for j in order:
        x, y = cols[j]
        u, v = (x,y) if j in side else (0,0)
        while x | y:
            i = (x | y).bit_length() - 1
            k = ((x >> i) & 1) + 2*((y >> i) & 1)
            if i not in pivots:
                inv = (0,1,3,2)[k]
                pivots[i] = mul(x,y,inv), mul(u,v,inv)
                break
            a,b = mul(*pivots[i][0],k)
            c,d = mul(*pivots[i][1],k)
            x,y,u,v = x^a,y^b,u^c,v^d
        else:
            if u | v:
                return u,v
    raise ArithmeticError("split has no marker")


def find_tree(private,height):
    """Return the verified split hierarchy around the distinguished uplift point."""
    if len(private) != len(height) or any(type(x) is not int or x<0 for x in private):
        raise ValueError("invalid private input")
    if any(type(h) is not int or h not in range(4) for h in height):
        raise ValueError("invalid height input")
    relations = dependencies(private)
    if len({combine(height,r) for r in relations} - {0}) < 2:
        raise ValueError("height rank below two")
    comps = [{i} for i in range(len(private))]
    for r in relations:
        indices = set(bits(r))
        merged = set.union(*(s for s in comps if s & indices))
        comps = [s for s in comps if not s & indices] + [merged]
    if len(comps) != 1:
        raise ValueError("private matroid must be connected")
    top = 1 << max(x.bit_length() for x in private)
    original = [(p | (top if h&1 else 0), top if h&2 else 0) for p,h in zip(private,height)]
    special = (top,0)
    cols = [special] + original
    nodes = [None] + list(range(len(private)))
    while (side := find_split(cols)) is not None:
        if 0 in side:
            side = set(range(len(cols))) - side
        port = _marker(cols,side)
        keep = sorted(set(range(len(cols))) - side)
        descendants = [nodes[i] for i in sorted(side)]
        cols = [cols[i] for i in keep] + [port]
        nodes = [nodes[i] for i in keep] + [descendants]
    if not three_connected(cols):
        raise ArithmeticError("invalid terminal central torso")

    # Recheck each physical cut against the original representation after all
    # marker replacements. Verify every central marker spans its original port.
    full = rank(original+[special])
    def verify(node):
        if type(node) is int:
            return [node]
        ids = [j for child in node for j in verify(child)]
        left = [original[j] for j in ids]
        right = [special]+[v for j,v in enumerate(original) if j not in ids]
        if rank(left)+rank(right)-full != 1:
            raise ArithmeticError("expanded tree split failed rank certificate")
        return ids
    seen = []
    for node,port in zip(nodes[1:],cols[1:]):
        ids = verify(node)
        seen.extend(ids)
        left = [original[j] for j in ids]
        right = [special]+[v for j,v in enumerate(original) if j not in ids]
        if (port==(0,0) or rank(left+[port])!=rank(left)
                or rank(right+[port])!=rank(right)):
            raise ArithmeticError("incorrect expanded marker")
    if sorted(seen)!=list(range(len(private))):
        raise ArithmeticError("lost physical indices")
    return nodes[1:]


def reduce_automatically(private,height,tag,three_name=None):
    tree = find_tree(private,height)
    return reduce_central(private,height,tag,tree,three_name)

