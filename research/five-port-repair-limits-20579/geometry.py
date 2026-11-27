"""Recover held products, paid OR supports and uncovered target cells."""


def require(condition, message):
    if not condition:
        raise ValueError(message)


def geometry(context, rows):
    """Return residual (row, column) pairs and free 64-input union masks."""
    gates = context["gates"]
    output = context["output"]
    removed = context["ports"]
    anchor = context["marker_source"]
    require(len(rows) == 32 and all(type(r) is int and 0 <= r < 1 << 32 for r in rows),
            "invalid target row words")
    require(all(r != (1 << 32) - 1 for r in rows) and
            all(any(not (r >> v & 1) for r in rows) for v in range(32)),
            "a row or column contains no zero")
    require(len(gates) == 180 and output == 243 and removed == [220, 223, 224, 225, 226]
            and anchor == 121, "unexpected geometric interface")
    for w, gate in enumerate(gates, 64):
        require(len(gate) == 3 and all(type(i) is int for i in gate)
                and gate[0] in (0, 1) and all(0 <= i < w for i in gate[1:]),
                "invalid gate or operand")

    # Peel the output OR network until its product leaves are exposed.
    products = set()
    pending = [output]
    while pending:
        w = pending.pop()
        require(w >= 64, "raw input reaches the output outside a product")
        op, a, b = gates[w - 64]
        if op == 0:
            products.add(w)
        else:
            pending.extend((a, b))
    held = products.difference(removed)
    require(len(products) == 16 and len(held) == 11, "expected five removed and eleven held products")

    supports = {i: 1 << i for i in range(64)}

    def support(w):
        if w not in supports:
            op, a, b = gates[w - 64]
            require(op == 1, "product operand depends on a non-OR gate")
            supports[w] = support(a) | support(b)
        return supports[w]

    def operands(w):
        _, a, b = gates[w - 64]
        return support(a), support(b)

    held_pairs = [operands(w) for w in sorted(held)]
    support(anchor)
    # Snapshot before visiting the removed products. Cost counts wire IDs,
    # whereas operand availability is a set of distinct Boolean supports.
    require(len(supports) - 64 == 114, "expected 114 paid OR gates")
    free = set(supports.values())
    removed_pairs = [operands(w) for w in removed]
    residual = set()
    for u, row in enumerate(rows):
        for v in range(32):
            point = (1 << u) | (1 << (32 + v))
            fixed = any(a & point and b & point for a, b in held_pairs)
            replaced = any(a & point and b & point for a, b in removed_pairs)
            target = bool(row >> v & 1)
            require((fixed or replaced) == target, "product union differs from target")
            if target and not fixed:
                residual.add((u, v))
    require(len(residual) == 98, "expected 98 residual cells")
    return residual, free
