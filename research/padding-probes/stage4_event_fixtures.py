"""Unbounded clique minors on original physical fibres with affine event records."""
from itertools import combinations

from event_fixtures import _slot_offsets
from padding_cnf import encode
from stack_alias import decode_alias


def record_codes(events):
    """Injective per-variable codes for this fixture on raw or macro records.

    The pre-state parity and marker choice determine every other record field
    at a fixed event. Prefix records are singletons. The output uses one bit.
    """
    codes = {}
    for vertex, domain in events.domains.items():
        if vertex == events.output:
            codes[vertex] = {bit: bit for bit in domain}
        else:
            local = {r: ((r.before[0] & 1) << 1) | (r.bit or 0) for r in domain}
            if len(set(local.values())) != len(local):
                raise ValueError("event records not uniquely determined by parity and marker")
            codes[vertex] = local
    return codes


def _parity_table(challenge, watched):
    n = len(watched) - 1
    first = encode(challenge, n, 0).count(b"\n") - len(watched)
    finished = first + 2 * len(watched)
    sink = 2 * (finished + 1)
    outputs = {q: int(q == 2 * finished + 1) for q in range(sink + 1)}
    table = {}
    for q in outputs:
        stage, parity = divmod(q, 2)
        for byte in range(256):
            if stage >= finished:
                dest = sink
            elif stage < first or (stage - first) % 2:
                dest = 2 * (stage + int(byte == 10)) + parity
            elif byte == 45 or 49 <= byte <= 57:
                watch = watched[(stage - first) // 2]
                dest = 2 * (stage + 1) + (parity ^ int(watch and byte == 45))
            else:
                dest = sink
            table[q, 0, byte] = (dest, "stay")
    return table, 0, 0, outputs


def affine_clique(t=5):
    """Return a full physical instance with a certified K_t minor, for t≥5.

    The t contiguous vertex blocks each list all its neighbors in increasing
    order. For edge ij the earlier block uses the positive ID and its mate uses
    the negative ID. The machine XORs all earlier physical signs and the enable.
    """
    if type(t) is not int or t < 5:
        raise ValueError("expected clique order at least five")
    edge_ids = {uv: 2003 + 29 * j for j, uv in enumerate(combinations(range(t), 2))}
    aliases = []
    watched = []
    blocks = []
    endpoints = {uv: [] for uv in edge_ids}
    for u in range(t):
        block = []
        for v in range(t):
            if v == u:
                continue
            uv = (u, v) if u < v else (v, u)
            i = len(aliases)
            endpoints[uv].append(i)
            block.append(i)
            aliases.append(edge_ids[uv] if u < v else -edge_ids[uv])
            watched.append(u < v)
        blocks.append(tuple(block))
    n = len(aliases)
    aliases.append(1)
    watched.append(True)
    challenge = [(1, -2, 3), (-1, 2, n)]
    table, initial, bottom, outputs = _parity_table(challenge, watched)
    slots, _ = _slot_offsets(challenge, n)
    pins = ((endpoints[0, 1][1], 0), (n, 1))
    samples = {}
    for varied in (0, 1):
        values = {edge_ids[0, 1]: 1, edge_ids[0, 2]: varied, 1: 1}
        key = sum((values.get(abs(a), 0) ^ int(a < 0)) << i for i, a in enumerate(aliases))
        raw = encode(challenge, n, key)
        decode_alias(raw, aliases)
        samples[varied] = raw
    return dict(challenge=challenge, n=n, aliases=aliases, table=table, initial=initial,
                bottom=bottom, outputs=outputs, occurrence_pins=pins, id_pins=(),
                schedule={}, macro_schedule=("stay",) * (n + 1), slot_events=slots,
                minor_slot_sets=tuple(blocks),
                minor_links={uv: tuple(pair) for uv, pair in endpoints.items()},
                raw_witnesses=samples, record_codes=record_codes)
