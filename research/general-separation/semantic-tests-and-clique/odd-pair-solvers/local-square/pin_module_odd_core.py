"""Exact module quotient for induced all-odd supports with protected literal pins.

Rows and witness masks use integer bits indexed by original vertex labels.
Core.rows uses compact indices; Core.representatives maps them back to labels.
"""
from dataclasses import dataclass
from itertools import combinations


def _sites(mask):
    while mask:
        bit = mask & -mask
        yield bit.bit_length() - 1
        mask ^= bit


def _checked_rows(rows):
    rows = tuple(rows)
    limit = 1 << len(rows)
    for i, row in enumerate(rows):
        if type(row) is not int or not 0 <= row < limit or row & (1 << i):
            raise ValueError("expected loop-free bounded integer adjacency masks")
    for i, row in enumerate(rows):
        if any(not (rows[j] & (1 << i)) for j in _sites(row)):
            raise ValueError("asymmetric adjacency")
    return rows


def _indices(vertices, n):
    vertices = tuple(vertices)
    if any(type(i) is not int or not 0 <= i < n for i in vertices):
        raise ValueError("invalid vertex label")
    if len(set(vertices)) != len(vertices):
        raise ValueError("duplicate vertex label")
    return vertices


def _closure(rows, first, second, forbidden=0):
    reference = rows[first]
    members = (1 << first) | (1 << second)
    pending = 1 << second
    while pending:
        bit = pending & -pending
        pending ^= bit
        new = (reference ^ rows[bit.bit_length() - 1]) & ~members
        if new & forbidden:
            return None
        members |= new
        pending |= new
    return members


def pair_module(rows, first, second):
    """Original-label mask of the least module containing two distinct vertices."""
    rows = _checked_rows(rows)
    _indices((first, second), len(rows))
    return _closure(rows, first, second)


def _require_witness(rows, pins, word):
    if type(word) is not int or not 0 <= word < (1 << len(rows)):
        raise ValueError("invalid witness mask")
    if any(not word & (1 << i) for i in pins):
        raise ValueError("missing compulsory vertex")
    if any((rows[i] & word).bit_count() % 2 == 0 for i in _sites(word)):
        raise ValueError("selected vertex has even degree")


@dataclass(frozen=True)
class Core:
    original_rows: tuple
    pins: tuple
    blocks: tuple
    representatives: tuple
    block_of: tuple
    rows: tuple
    pin_indices: tuple

    def project(self, word):
        """Return the compact quotient witness, checked before and after."""
        _require_witness(self.original_rows, self.pins, word)
        result = sum(((word & block).bit_count() % 2) << j
                     for j, block in enumerate(self.blocks))
        _require_witness(self.rows, self.pin_indices, result)
        return result

    def lift(self, word):
        """Choose the literal original representative of each selected block."""
        _require_witness(self.rows, self.pin_indices, word)
        result = sum(1 << self.representatives[j] for j in _sites(word))
        _require_witness(self.original_rows, self.pins, result)
        return result


def build_core(rows, pins):
    rows = _checked_rows(rows)
    n = len(rows)
    pins = _indices(pins, n)
    protected = sum(1 << i for i in pins)
    parents = list(range(n))

    def find(i):
        while parents[i] != i:
            parents[i] = parents[parents[i]]
            i = parents[i]
        return i

    free = tuple(i for i in range(n) if not protected & (1 << i))
    for i, j in combinations(free, 2):
        if find(i) == find(j):
            continue
        members = _closure(rows, i, j, protected)
        if members is not None:
            root = find(i)
            for v in _sites(members):
                parents[find(v)] = root

    partition = {}
    for i in range(n):
        root = find(i)
        partition[root] = partition.get(root, 0) | (1 << i)
    blocks = tuple(partition.values())  # Ordered by smallest original label.
    reps = tuple((block & -block).bit_length() - 1 for block in blocks)
    block_of = [0] * n
    for j, block in enumerate(blocks):
        for v in _sites(block):
            block_of[v] = j
    compact = tuple(sum(1 << j for j, v in enumerate(reps) if rows[u] & (1 << v))
                    for u in reps)
    return Core(rows, pins, blocks, reps, tuple(block_of), compact,
                tuple(block_of[v] for v in pins))


def solve(rows, p, q):
    """Quartic quotient dispatch. Return (YES, raw mask), (NO,None), or (UNKNOWN,None)."""
    from quartic_window_solver import solve as solve_quartic

    core = build_core(rows, (p, q))
    if any(row.bit_count() > 4 for row in core.rows):
        return "UNKNOWN", None
    status, word = solve_quartic(core.rows, *core.pin_indices)
    if status == "YES":
        return status, core.lift(word)
    return status, None


def _regression():
    def graph(n, edges):
        rows = [0] * n
        for a, b in edges:
            rows[a] |= 1 << b
            rows[b] |= 1 << a
        return tuple(rows)

    def check_words(core):
        for rows, pins, convert in ((core.rows, core.pin_indices, core.lift),
                                    (core.original_rows, core.pins, core.project)):
            for word in range(1 << len(rows)):
                try:
                    _require_witness(rows, pins, word)
                except ValueError:
                    continue
                convert(word)

    for length in (4, 5):
        # Replace the second vertex of a path by C5 (no internal twin pair).
        parts = [[0], list(range(1, 6))] + [[j] for j in range(6, length + 4)]
        edges = [(v, 1 + v % 5) for v in range(1, 6)]
        edges.extend((a, b) for s, t in zip(parts, parts[1:]) for a in s for b in t)
        rows = graph(length + 4, edges)
        pins = (0, length + 3)
        core = build_core(rows, pins)
        assert 62 in core.blocks and len(core.blocks) == length
        assert pair_module(rows, 1, 2) == 62
        check_words(core)
        assert solve(rows, *pins)[0] == ("NO" if length == 4 else "YES")

    # Both members of a true twin pair can be selected (edge), as can two
    # false twins (the two leaves of a claw with another selected leaf).
    for rows, pins, twins in [(graph(4, [(0, 1), (2, 3)]), (2, 3), 3),
                              (graph(4, [(0, 3), (1, 3), (2, 3)]), (2, 3), 3)]:
        core = build_core(rows, pins)
        assert twins in core.blocks and core.project(15) == core.project(15 ^ twins)
        check_words(core)


if __name__ == "__main__":
    _regression()
    print("OK")
