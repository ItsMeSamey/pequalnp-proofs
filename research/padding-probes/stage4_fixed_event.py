"""Fixed raw sign-parity automata on physical clique-minor families."""
from itertools import combinations

from event_fixtures import _slot_offsets
from padding_cnf import encode
from stack_alias import decode_alias
from stage4_event_fixtures import record_codes


def sign_table(*, odd_lines=False):
    """XOR minus signs at line start, optionally only on lines of odd index."""
    if type(odd_lines) is not bool:
        raise ValueError("odd_lines must be Boolean")
    outputs = {q: q & 1 for q in range(8 if odd_lines else 4)}
    table = {}
    for q in outputs:
        parity = q & 1
        first = (q >> 1) & 1
        phase = q >> 2
        for byte in range(256):
            lf = int(byte == 10)
            watched = not odd_lines or phase == 1
            after = parity ^ int(first and watched and byte == 45)
            new_phase = (phase ^ lf) if odd_lines else 0
            table[q, 0, byte] = ((new_phase << 2) | (lf << 1) | after, "stay")
    return table, 2, 0, outputs


def fixed_clique(t=5, *, paired=True):
    """Same table across t: eight states for paired IDs, four for triple IDs."""
    if type(t) is not int or t < 5 or type(paired) is not bool:
        raise ValueError("expected clique order at least five and a Boolean option")
    pairs = list(combinations(range(t), 2))
    names = {uv: (2003 + 74 * j, 2040 + 74 * j) for j, uv in enumerate(pairs)}
    aliases = []
    blocks = []
    endpoints = {}
    for u in range(t):
        start = len(aliases)
        for v in range(t):
            if u == v:
                continue
            uv = (u, v) if u < v else (v, u)
            e, f = names[uv]
            if paired:
                group = (e, f) if u < v else (-f, -e)
            else:
                group = (e, e) if u < v else (-e,)
            for alias in group:
                endpoints.setdefault(abs(alias), []).append(len(aliases))
                aliases.append(alias)
        blocks.append(tuple(range(start, len(aliases))))
    n = len(aliases)
    aliases.append(1)
    challenge = [(1, -2, 3), (-1, 2, n)]
    table, initial, bottom, outputs = sign_table(odd_lines=paired)
    slots, _ = _slot_offsets(challenge, n)
    fixed = names[0, 1][0]
    pins = ((endpoints[fixed][-1], 0), (n, 1))
    samples = {}
    for varied in (0, 1):
        values = {fixed: 1, names[0, 2][0]: varied, 1: 1}
        key = sum((values.get(abs(a), 0) ^ int(a < 0)) << i for i, a in enumerate(aliases))
        raw = encode(challenge, n, key)
        decode_alias(raw, aliases)
        prediction = int(not paired) ^ (len(pairs) & 1) ^ varied
        samples[prediction] = raw
    links = {uv: tuple(endpoints[e][-2:]) for uv, (e, _) in names.items()}
    return dict(challenge=challenge, n=n, aliases=aliases, table=table,
                initial=initial, bottom=bottom, outputs=outputs, occurrence_pins=pins,
                id_pins=(), schedule={}, macro_schedule=("stay",) * (n + 1),
                slot_events=slots, minor_slot_sets=tuple(blocks), minor_links=links,
                raw_witnesses=samples, record_codes=record_codes)
