"""Rank-compressed binary syndrome DP for disjoint biclique conflict components."""
from itertools import product
from biclique_period import _basis, _reduce, _solve


def _indices(x):
    while x:
        bit = x & -x
        yield bit.bit_length() - 1
        x ^= bit


def _compress(rows, target):
    basis = _basis(rows)
    pivots = sorted(basis, reverse=True)

    def encode(x):
        code = 0
        for i, p in enumerate(pivots):
            if x >> p & 1:
                x ^= basis[p]
                code |= 1 << i
        return None if x else code

    return [encode(x) for x in rows], encode(target), len(pivots)


def _pieces(columns, groups, rank):
    parent = list(range(rank))

    def root(i):
        while parent[i] != i:
            parent[i] = parent[parent[i]]
            i = parent[i]
        return i

    owners = []
    for pair in groups:
        mask = 0
        for shore in pair:
            for i in shore:
                mask |= columns[i]
        bits = iter(_indices(mask))
        first = next(bits, None)
        owners.append(first)
        if first is not None:
            for i in bits:
                parent[root(i)] = root(first)
    coords = {}
    grouped = {}
    for i in range(rank):
        coords.setdefault(root(i), []).append(i)
    for i, owner in enumerate(owners):
        if owner is not None:
            grouped.setdefault(root(owner), []).append(i)
    return [(coords[r], ids) for r, ids in grouped.items()]


_PERM = tuple(bytes(sum(((b >> i) & 1) << (i ^ s) for i in range(8))
                    for b in range(256)) for s in range(8))


def _extend(bits, v):
    high = v >> 3
    perm = _PERM[v & 7]
    result = bytearray(len(bits))
    for i, b in enumerate(bits):
        result[i] = b | perm[bits[i ^ high]]
    return result


def _close(bits, basis):
    for v in basis:
        bits = _extend(bits, v)
    return bits


def _has(bits, t):
    return bits[t >> 3] >> (t & 7) & 1


def _dp(shores, target, rank):
    width = 1 << max(0, rank - 3)
    history = [bytearray(width)]
    history[0][0] = 1
    for left, right in shores:
        prev = history[-1]
        a = _close(prev, left)
        b = _close(prev, right)
        joined = bytearray(width)
        for i in range(width):
            joined[i] = a[i] | b[i]
        history.append(joined)
        del a, b
    if not _has(history[-1], target):
        return None
    choices = [0] * len(shores)
    for g in reversed(range(len(shores))):
        prev = history[g]
        for side, basis in enumerate(shores[g]):
            prefixes = [prev]
            for v in basis:
                prefixes.append(_extend(prefixes[-1], v))
            if _has(prefixes[-1], target):
                choices[g] = side
                for j in reversed(range(len(basis))):
                    if not _has(prefixes[j], target):
                        target ^= basis[j]
                break
        else:
            raise AssertionError("reachable syndrome has no predecessor")
    return choices


def _orient(shores, target):
    for choices in product((0, 1), repeat=len(shores)):
        basis = _basis(v for pair, side in zip(shores, choices) for v in pair[side])
        if not _reduce(target, basis):
            return choices
    return None


def syndrome_witness(columns, target, components, *, method="auto", max_dp_bytes=None):
    """Find original flags. Shore and isolated-flag semantics match biclique_dual.

    Auto chooses packed DP for local rank r <= local group count g, subject
    to the optional byte budget, otherwise orientation enumeration. With
    explicit dp, exceeding the budget raises MemoryError. Budget covers raw
    DP bitset payload, excluding Python allocation overhead, the fixed 2048
    byte lookup table and polynomial Gaussian, coordinate and input storage.

    For B=max(1,2**r/8) bytes and local shore basis ranks summing to S,
    DP uses O((g+S)*B) indexed byte operations, and at most (g+r+4)*B
    payload bytes. Address arithmetic adds its bit cost on a bit machine.
    Parts run sequentially. Original-coordinate Gaussian lifting is polynomial.
    """
    if method not in ("dp", "orientation", "auto"):
        raise ValueError("expected auto, dp, or orientation")
    if max_dp_bytes is not None and (not isinstance(max_dp_bytes, int) or max_dp_bytes < 0):
        raise ValueError("invalid bitset byte budget")
    columns = tuple(columns)
    if not isinstance(target, int) or target < 0 or any(
        not isinstance(v, int) or v < 0 for v in columns
    ):
        raise ValueError("invalid syndrome mask")
    used = bytearray(len(columns))
    groups = []
    for left, right in components:
        pair = tuple(left), tuple(right)
        for shore in pair:
            for i in shore:
                if not isinstance(i, int) or not 0 <= i < len(columns) or used[i]:
                    raise ValueError("invalid or repeated flag index")
                used[i] = 1
        groups.append(pair)
    fixed = [i for i in range(len(columns)) if not used[i]]
    free = _basis(columns[i] for i in fixed)
    reduced = [_reduce(v, free) for v in columns]
    compressed, t, rank = _compress(reduced, _reduce(target, free))
    if t is None:
        return None
    chosen = [0] * len(groups)
    for coords, ids in _pieces(compressed, groups, rank):
        def local(x):
            return sum(((x >> i) & 1) << j for j, i in enumerate(coords))

        shores = [
            tuple(tuple(_basis(local(compressed[i]) for i in shore).values())
                  for shore in groups[g])
            for g in ids
        ]
        r = len(coords)
        use_dp = method == "dp" or (method == "auto" and r <= len(ids))
        if use_dp and max_dp_bytes is not None:
            estimate = (len(ids) + r + 4) << max(0, r - 3)
            if estimate > max_dp_bytes:
                if method == "dp":
                    raise MemoryError("DP bitset byte budget exceeded")
                use_dp = False
        choices = _dp(shores, local(t), r) if use_dp else _orient(shores, local(t))
        if choices is None:
            return None
        for g, side in zip(ids, choices):
            chosen[g] = side
    for pair, side in zip(groups, chosen):
        fixed.extend(pair[side])
    witness = _solve(columns, fixed, target)
    if witness is None:
        raise AssertionError("chosen quotient orientations must lift")
    return witness
