"""Bit-mask solver for x_i (A x)_i = 0 with an odd linear marker."""
from collections import deque


def bits(mask):
    while mask:
        bit = mask & -mask
        yield bit.bit_length() - 1
        mask ^= bit


def components(rows):
    n = len(rows)
    reach = [row | (1 << i) for i, row in enumerate(rows)]
    for k in range(n):
        for i in range(n):
            if reach[i] >> k & 1:
                reach[i] |= reach[k]
    # Strict successors reach fewer vertices in the condensation DAG.
    unseen = (1 << n) - 1
    for i in sorted(range(n), key=lambda i: reach[i].bit_count()):
        if unseen >> i & 1:
            group = sum(1 << j for j in bits(reach[i]) if reach[j] >> i & 1)
            unseen ^= group
            yield group


def local_models(rows, group, marked):
    for i in bits(group & ~marked):
        yield 1 << i
    for root in bits(marked):
        seen = 1 << root
        queue = deque([(root, seen)])
        while queue:
            u, path = queue.popleft()
            for v in bits(rows[u] & group & ~seen):
                bit = 1 << v
                seen |= bit
                if marked & bit:
                    # Direct edges are shortest paths too. A rooted BFS path
                    # is induced in the graph with other marked interiors barred.
                    yield path | bit
                else:
                    queue.append((v, path | bit))


def model_basis(rows):
    """Return independent actual models spanning all models, or raise ValueError."""
    rows = tuple(rows)
    if any(row < 0 or row >= 1 << len(rows) for row in rows):
        raise ValueError("row outside matrix")
    basis = []
    pivots = {}
    for group in components(rows):
        nodes = list(bits(group))
        if any(not rows[j] >> i & 1 for i in nodes for j in bits(rows[i] & group)):
            raise ValueError("asymmetric internal edge")
        diagonal = sum(1 << i for i in nodes if rows[i] >> i & 1)
        contexts = [(0, diagonal)]
        for s in basis:
            shift = sum(1 << i for i in nodes if (rows[i] & s).bit_count() % 2)
            if shift:
                contexts.append((s, diagonal ^ shift))
                break
        for s, marked in contexts:
            for local in local_models(rows, group, marked):
                model = s | local
                reduced = model
                while reduced:
                    pivot = reduced.bit_length() - 1
                    if pivot not in pivots:
                        pivots[pivot] = reduced
                        basis.append(model)
                        break
                    reduced ^= pivots[pivot]
    return basis


def symmetric_switch(rows, marker):
    """Return marker-equivalent symmetric rows, or None if no such switch exists."""
    if not marker:
        return None
    anchor = (marker & -marker).bit_length() - 1
    flips = [(row >> anchor ^ rows[anchor] >> i) & 1 for i, row in enumerate(rows)]
    # Adding u_i * (marker.x + 1) to active guard i adds the constant
    # as a diagonal bit because Boolean x_i^2 = x_i.
    switched = [row ^ ((marker ^ (1 << i)) if flips[i] else 0)
                for i, row in enumerate(rows)]
    if all(switched[i] >> j & 1 == switched[j] >> i & 1
           for i in range(len(rows)) for j in range(i)):
        return switched
    return None


def witness(rows, marker):
    """Return a model with odd marker, None for UNSAT, or raise outside the class."""
    rows = tuple(rows)
    if not 0 <= marker < 1 << len(rows):
        raise ValueError("marker outside matrix")
    if any(not 0 <= row < 1 << len(rows) for row in rows):
        raise ValueError("row outside matrix")
    if not marker:
        return None
    try:
        basis = model_basis(rows)
    except ValueError:
        switched = symmetric_switch(rows, marker)
        if switched is None:
            raise
        basis = model_basis(switched)
    return next((model for model in basis if (model & marker).bit_count() % 2), None)
