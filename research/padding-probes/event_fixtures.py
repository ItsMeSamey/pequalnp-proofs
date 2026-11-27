"""Original DIMACS controls and supplied decompositions for the byte-event CSP."""
from heapq import heapify, heappop, heappush

from padding_cnf import encode
from stack_align_padding import _comparator
from stack_alias import decode_alias


def _small_bags(size, edges, anchor):
    """Eliminate degree ≤2 after removing an optional common anchor, then restore it."""
    neighbors = {v: set() for v in range(size) if v != anchor}
    for u, v in edges:
        if u != anchor and v != anchor and u != v:
            neighbors[u].add(v)
            neighbors[v].add(u)
    ready = [v for v, ns in neighbors.items() if len(ns) <= 2]
    heapify(ready)
    saved = []
    while ready:
        v = heappop(ready)
        if v not in neighbors or len(neighbors[v]) > 2:
            continue
        ns = sorted(neighbors.pop(v))
        saved.append((v, ns))
        for u in ns:
            neighbors[u].remove(v)
            neighbors[u].update(w for w in ns if w != u)
            if len(neighbors[u]) <= 2:
                heappush(ready, u)
    if neighbors:
        raise AssertionError("fixture exceeds its asserted two-neighbor elimination bound")
    index = {v: i for i, (v, _) in enumerate(saved)}
    bags = []
    links = []
    for i, (v, ns) in enumerate(saved):
        bag = [v, *ns]
        if anchor is not None:
            bag.append(anchor)
        bags.append(tuple(bag))
        if ns:
            links.append((i, min(index[u] for u in ns)))
        elif i + 1 < len(saved):
            links.append((i, len(saved) - 1))
    return bags, links


def _slot_offsets(challenge, n):
    lines = encode(challenge, n, 0).splitlines(keepends=True)
    start = sum(map(len, lines[:-(n + 1)]))
    offsets = []
    for line in lines[-(n + 1):]:
        offsets.append(start)
        start += len(line)
    return tuple(offsets), start


def _build(h, mismatch, gate, nested):
    if type(h) is not int or h < 1 or type(mismatch) is not bool or type(gate) is not bool:
        raise ValueError("expected positive depth and Boolean options")
    challenge = []
    if nested:
        # Exterior native pair encloses h alias pairs without changing native height.
        opens = list(range(1, h + 2))
        aliases = opens + list(reversed(opens))
        close = len(aliases) - 1
    else:
        # Two rails A and B; every signed alias joins corresponding rung endpoints.
        opens = list(range(1, h + 1))
        aliases = opens + opens
        close = h
    if mismatch:
        aliases[close] *= -1
    n = len(aliases)
    aliases.append(len(opens) + 1)
    actions = ["ignore"] * n + ["gate" if gate else "ignore"]
    actions[0], actions[close] = "push", "pop"
    table, initial, bottom, outputs = _comparator(challenge, actions)
    slots, length = _slot_offsets(challenge, n)
    edges = {(i, i + 1) for i in range(length)}
    first = {}
    for j, alias in enumerate(aliases):
        name = abs(alias)
        if name in first:
            edges.add((first[name], slots[j]))
        else:
            first[name] = slots[j]
    edges.add((slots[0], slots[close]))
    anchor = None if nested else slots[close]
    bags, links = _small_bags(length + 1, edges, anchor)
    witnesses = {}
    for enable in (0, 1):
        key = sum(int(a < 0) << j for j, a in enumerate(aliases[:-1])) | (enable << n)
        raw = encode(challenge, n, key)
        decode_alias(raw, aliases)
        witnesses[int(not mismatch and (not gate or enable))] = raw
    return dict(challenge=challenge, n=n, aliases=aliases, occurrence_pins=(), id_pins=(),
                table=table, initial=initial, bottom=bottom, outputs=outputs,
                schedule={slots[0]: "push", slots[close]: "pop"}, slot_events=slots,
                bags=bags, tree_edges=links, raw_witnesses=witnesses)


def crossing_ladder(h=2, *, mismatch=False, gate=True):
    """Width ≤3 for the path and h crossing alias rungs, after restoring one anchor."""
    return _build(h, mismatch, gate, False)


def nested_skew(h=2, *, mismatch=False, gate=True):
    """Width ≤2 for nested alias scopes at unchanged native depth one."""
    return _build(h, mismatch, gate, True)


def state_dependent():
    """Two accessible controls on the same physical byte and bottom need different ops."""
    challenge = []
    n = 2
    aliases = [1, 2, 3]
    table, initial, bottom, outputs = _comparator(challenge, ["gate", "push", "gate"])
    slots, length = _slot_offsets(challenge, n)
    prefix_lines = encode(challenge, n, 0).count(b"\n") - (n + 1)
    failed_second = 2 * (prefix_lines + 2) + 1
    for top in (0, 1, 2):
        for byte in (45, *range(49, 58)):
            dest, _, _ = table[failed_second, top, byte]
            table[failed_second, top, byte] = (dest, "stay")
    path = [(i, i + 1) for i in range(length)]
    bags, links = _small_bags(length + 1, path, None)
    witnesses = {0: encode(challenge, n, 4), 1: encode(challenge, n, 5)}
    return dict(challenge=challenge, n=n, aliases=aliases, occurrence_pins=(), id_pins=(),
                table=table, initial=initial, bottom=bottom, outputs=outputs,
                schedule={slots[1]: "push"}, slot_events=slots,
                bags=bags, tree_edges=links, raw_witnesses=witnesses)
