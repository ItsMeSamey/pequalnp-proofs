"""Physical signed marker ladders linked by byte-path bridges."""
from event_fixtures import _small_bags, _slot_offsets
from padding_cnf import encode
from stack_align_padding import _comparator
from stack_alias import decode_alias


def block_ladders(blocks=2, h=3):
    """Each block compares the restored A0 value with the physical B1 marker."""
    if type(blocks) is not int or blocks < 2 or type(h) is not int or h < 3:
        raise ValueError("at least two ladders of at least three rungs required")
    n = 2 * h * blocks
    challenge = [(1, -2, 3), (-1, 2, n)]
    aliases = []
    actions = ["ignore"] * n + ["gate"]
    pins = []
    for block in range(blocks):
        names = []
        for j in range(h):
            name = 1009 + 37 * (block * h + j)
            names.append(-name if (block + j) % 2 else name)
        aliases.extend(names + names)
        base = 2 * h * block
        actions[base] = actions[base + 1] = "push"
        actions[base + h] = actions[base + h + 1] = "pop"
        pins.append((base + 1, 1))
    aliases.append(1)
    pins.append((n, 1))
    table, initial, bottom, outputs = _comparator(challenge, actions)
    slots, length = _slot_offsets(challenge, n)
    prefix_count = encode(challenge, n, 0).count(b"\n") - n - 1
    chords = set()
    minors = []
    for block in range(blocks):
        base = 2 * h * block
        for j in range(h):
            chords.add((slots[base + j], slots[base + h + j]))
        chords.add((slots[base + 1], slots[base + h]))
        chords.add((slots[base], slots[base + h + 1]))
        # In slot coordinates after contracting the byte chains, branch sets
        # A1, A2..A_last, {A0,B0}, {B1,B2} give K4 on just the path and rungs.
        minors.append(((base + 1,), tuple(range(base + 2, base + h)),
                       (base, base + h), (base + h + 1, base + h + 2)))
        stage = prefix_count + 2 * (base + h)
        for bad in (0, 1):
            for top in (1, 2):
                for byte in (45, *range(49, 58)):
                    # Discard the inner symbol at B0, preserving the actual
                    # stack and sticky failure bit. B1 then inspects saved A0.
                    table[2 * stage + bad, top, byte] = (2 * (stage + 1) + bad, "pop")
    boundaries = [0] + [slots[2 * h * j] for j in range(1, blocks)] + [length + 1]
    bags, links, bridges = [], [], []
    previous_tail = None
    for block, (lo, end) in enumerate(zip(boundaries, boundaries[1:])):
        local_edges = {(i, i + 1) for i in range(end - lo - 1)}
        local_edges.update((u - lo, v - lo) for u, v in chords if lo <= u < v < end)
        anchor = slots[2 * h * block + h] - lo
        piece, piece_links = _small_bags(end - lo, local_edges, anchor)
        offset = len(bags)
        bags.extend(tuple(lo + v for v in bag) for bag in piece)
        links.extend((offset + x, offset + y) for x, y in piece_links)
        first = offset + next(i for i, bag in enumerate(piece) if 0 in bag)
        last = offset + next(i for i, bag in enumerate(piece) if end - lo - 1 in bag)
        if previous_tail is not None:
            bridge = (lo - 1, lo)
            bridges.append(bridge)
            index = len(bags)
            bags.append(bridge)
            links.extend(((previous_tail, index), (index, first)))
        previous_tail = last

    yes = 1 << n
    for block in range(blocks):
        base = 2 * h * block
        for j in (0, 1, h, h + 1):
            yes |= 1 << (base + j)
    no = yes ^ 1 ^ (1 << h)
    witnesses = {1: encode(challenge, n, yes), 0: encode(challenge, n, no)}
    for raw in witnesses.values():
        decode_alias(raw, aliases)
    macro_schedule = tuple(op if op in ("push", "pop") else "stay" for op in actions)
    schedule = {p: op for p, op in zip(slots, macro_schedule) if op != "stay"}
    return dict(challenge=challenge, n=n, aliases=aliases, occurrence_pins=tuple(pins),
                id_pins=(), table=table, initial=initial, bottom=bottom, outputs=outputs,
                schedule=schedule, macro_schedule=macro_schedule, slot_events=slots,
                bags=bags, tree_edges=links, bridges=tuple(bridges),
                minor_slot_sets=tuple(minors), raw_witnesses=witnesses)
