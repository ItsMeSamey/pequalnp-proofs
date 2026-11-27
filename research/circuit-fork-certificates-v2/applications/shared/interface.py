"""Reconstruct the assigned five-port Boolean interface from its frozen circuit."""


def require(condition, message):
    if not condition:
        raise ValueError(message)


def reconstruct(context, rows):
    """Return the positive and negative 26-bit signature sets in bank order."""
    gates = context["gates"]
    ports = context["ports"]
    bank = context["bank"]
    output = context["output"]
    marker = context["marker_source"]
    require(len(rows) == 32 and all(type(r) is int and 0 <= r < 2**32 for r in rows),
            "expected 32 unsigned row words")
    require(len(gates) == 180 and output == 243 and marker == 121, "wrong circuit interface")
    require(ports == [220, 223, 224, 225, 226], "wrong port order")
    require(len(bank) == 26 and all(type(w) is int and 0 <= w <= output for w in bank)
            and len(set(bank)) == 26 and marker in bank, "invalid feature bank")
    for w, gate in enumerate(gates, 64):
        require(len(gate) == 3 and all(type(x) is int for x in gate), "malformed gate")
        op, a, b = gate
        require(op in (0, 1) and 0 <= a < w and 0 <= b < w, "invalid op or operand")

    def ancestors(roots, stops):
        found = set()
        pending = list(roots)
        while pending:
            w = pending.pop()
            if w >= 64 and w not in found and w not in stops:
                found.add(w)
                pending.extend(gates[w - 64][1:])
        return found

    fixed = ancestors([output, marker], set(ports))
    require(len(fixed) == 140, "expected 140 fixed gates before the paid marker")
    require(not (ancestors(bank, set()) & set(ports)), "bank depends on a replaced port")
    require(all(w < 64 or w in fixed for w in bank), "bank requires an unpaid gate")
    full = (1 << 1024) - 1
    inputs = [((1 << 32) - 1) << (32 * u) for u in range(32)]
    inputs.extend(sum(1 << (32 * u + v) for u in range(32)) for v in range(32))

    def replay(forced):
        values = inputs.copy()
        for w, (op, a, b) in enumerate(gates, 64):
            if w in forced:
                value = forced[w]
            elif op == 0:
                value = values[a] & values[b]
            else:
                value = values[a] | values[b]
            values.append(value)
        return values

    target = sum(r << (32 * u) for u, r in enumerate(rows))
    baseline = replay({})
    require(baseline[output] == target, "baseline disagrees with graph")
    marker_bits = full ^ baseline[marker]
    shard = sum(((marker_bits >> (33 * k)) & 1) << k for k in range(6))
    require(shard == 53, "paid marker has wrong shard")

    good = []
    for assignment in range(32):
        forced = {w: full if assignment & (1 << j) else 0 for j, w in enumerate(ports)}
        good.append(full ^ (replay(forced)[output] ^ target))
    require(all(mask == good[1] for mask in good[2:]), "nonzero port assignments disagree")
    zero, nonzero = good[:2]
    require((zero | nonzero) == full, "some cell admits no assignment")
    pos_cells = nonzero & ~zero
    neg_cells = zero & ~nonzero
    require((pos_cells.bit_count(), neg_cells.bit_count(), (zero & nonzero).bit_count())
            == (98, 613, 313), "wrong raw cell partition")

    def signatures(mask):
        return {sum(((baseline[w] >> i) & 1) << j for j, w in enumerate(bank))
                for i in range(1024) if mask & (1 << i)}

    positive, negative = signatures(pos_cells), signatures(neg_cells)
    require(not positive & negative and (len(positive), len(negative)) == (92, 427),
            "wrong projected signature partition")
    # Every feature has opposing required labels at Hamming distance one.
    require(all(any((p ^ (1 << j)) in negative for p in positive) for j in range(26)),
            "an essential feature lacks its opposite-label witness")

    # One new merged function drives the first port; all other ports read false.
    # Simplify old gates by the Boolean zero identities, then count those
    # reachable from the output or needed for any paid signal or the anchor.
    zero_wire, merged_wire = -1, -2
    aliases = dict(zip(ports, [merged_wire] + [zero_wire] * 4))
    retained = {}
    def simplify(i):
        if i < 64:
            return i
        if i not in aliases:
            op, a, b = gates[i - 64]
            a, b = simplify(a), simplify(b)
            if zero_wire in (a, b):
                aliases[i] = (b if a == zero_wire else a) if op == 1 else zero_wire
            elif a == b:
                aliases[i] = a
            else:
                aliases[i] = i
                retained[i] = (a, b)
        return aliases[i]
    stack = [simplify(i) for i in [output, marker, *bank]]
    reached = set()
    while stack:
        i = stack.pop()
        if i in retained and i not in reached:
            reached.add(i)
            stack.extend(retained[i])
    require(len(reached) == 136, "merged context does not retain 136 old gates")
    return positive, negative
