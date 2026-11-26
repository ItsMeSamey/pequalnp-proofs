"""Matching-guard witnesses. Labels 0, 1, 2 select zero, first, second."""
from collections import deque
from itertools import product


class Basis:
    def __init__(self):
        self.rows = {}

    def reduce(self, x):
        coefficients = 0
        for p in sorted(self.rows, reverse=True):
            if x >> p & 1:
                y, mask = self.rows[p]
                x ^= y
                coefficients ^= mask
        return x, coefficients

    def add(self, x, mask=0):
        x, combination = self.reduce(x)
        if x:
            self.rows[x.bit_length() - 1] = x, mask ^ combination
        return bool(x)


def certificate(pairs):
    """Return selected column IDs and a tight group subset J."""
    columns = [x for pair in pairs for x in pair]
    selected = set()
    while True:
        owner = {e // 2: e for e in selected}
        basis = Basis()
        for e in sorted(selected):
            added = basis.add(columns[e], 1 << e)
            assert added
        queue = deque(e for e in range(len(columns)) if e // 2 not in owner)
        parent = dict.fromkeys(queue)
        while queue:
            e = queue.popleft()
            if e in selected:
                neighbors = [e ^ 1]
            else:
                residual, dependency = basis.reduce(columns[e])
                if residual:
                    break
                neighbors = [s for s in sorted(selected) if dependency >> s & 1]
            for f in neighbors:
                if f not in parent:
                    queue.append(f)
                    parent[f] = e
        else:
            return sorted(selected), sorted({e // 2 for e in parent})
        while e is not None:
            selected.symmetric_difference_update([e])
            e = parent[e]


def kernelize(pairs, h):
    """Return (projected pairs, target, dimension, lift), or None if inconsistent."""
    whole = Basis()
    for pair in pairs:
        for x in pair:
            if x < 0:
                raise ValueError("expected nonnegative binary vectors")
            whole.add(x)
    if h < 0:
        raise ValueError("expected nonnegative target")
    if whole.reduce(h)[0]:
        return None
    selected, groups = certificate(pairs)
    if len(selected) == len(whole.rows):
        groups = range(len(pairs))
    inside = set(groups)
    outside = [i for i in range(len(pairs)) if i not in inside]
    basis = Basis()
    for e in selected:
        if e // 2 in inside:
            added = basis.add(pairs[e // 2][e % 2], 1 << e)
            assert added
    quotient = Basis()
    projected = []
    for i in outside:
        pair = []
        for x in pairs[i]:
            y = basis.reduce(x)[0]
            remainder, mask = quotient.reduce(y)
            if remainder:
                mask = 1 << len(quotient.rows)
                quotient.add(y, mask)
            pair.append(mask)
        projected.append(tuple(pair))
    remainder, target = quotient.reduce(basis.reduce(h)[0])
    assert not remainder

    def lift(labels):
        witness = [0] * len(pairs)
        discrepancy = h
        for i, label in zip(outside, labels, strict=True):
            witness[i] = label
            if label:
                discrepancy ^= pairs[i][label - 1]
        remainder, mask = basis.reduce(discrepancy)
        if remainder:
            raise ValueError("invalid quotient witness")
        for e in selected:
            if mask >> e & 1:
                witness[e // 2] = 1 + e % 2
        return witness

    return projected, target, len(quotient.rows), lift


def cover(b):
    """Greedily select boxes. Each tuple records the excluded symbol per position."""
    words = list(product(range(3), repeat=b))
    masks = [sum(1 << j for j, w in enumerate(words) if
                 all(a != v for a, v in zip(box, w))) for box in words]
    unseen = (1 << len(words)) - 1
    boxes = []
    while unseen:
        best = max(range(len(words)), key=lambda j: (unseen & masks[j]).bit_count())
        boxes.append(words[best])
        unseen &= ~masks[best]
    return boxes


def solve(pairs, h, block=None):
    result = kernelize(pairs, h)
    if result is None:
        return None
    pairs, h, _, lift = result
    m = len(pairs)
    if block is None:
        block = max(1, (m + 15) // 16)
    if block < 1:
        raise ValueError("expected positive block size")
    choices = [(0, 1, 2) for _ in pairs]
    covers = {}
    chunks = []
    for start in range(0, m, block):
        size = min(block, m - start)
        if size not in covers:
            covers[size] = cover(size)
        chunks.append(covers[size])
    for boxes in product(*chunks):
        excluded = [v for box in boxes for v in box]
        options = [[a for a in abc if a != x] for abc, x in zip(choices, excluded)]
        target = h
        basis = Basis()
        for i, ((a, b), pair) in enumerate(zip(options, pairs)):
            values = (0, *pair)
            target ^= values[a]
            basis.add(values[a] ^ values[b], 1 << i)
        residual, mask = basis.reduce(target)
        if not residual:
            return lift([ab[mask >> i & 1] for i, ab in enumerate(options)])
    return None
