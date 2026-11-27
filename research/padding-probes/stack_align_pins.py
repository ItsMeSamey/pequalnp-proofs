"""Pin-normalized byte charts and original completions for nested signed aliases."""
from collections.abc import Mapping

from padding_cnf import encode, parse
from stack_alias import _slots, decode_alias
from stack_align_padding import annotated_dag


def _pairs(pins):
    entries = pins.items() if isinstance(pins, Mapping) else pins
    try:
        entries = list(entries)
    except TypeError as exc:
        raise ValueError("expected a mapping or sequence of pins") from exc
    for entry in entries:
        if not isinstance(entry, (tuple, list)) or len(entry) != 2:
            raise ValueError("expected an (index, bit) pin")
        index, bit = entry
        if type(index) is not int or type(bit) is not int or bit not in (0, 1):
            raise ValueError("expected integer index and binary value")
        yield index, bit


def _fixed(slots, occurrence_pins, id_pins):
    known = {name for name, _ in slots}
    fixed = {}
    conflict = False
    for name, value in _pairs(id_pins):
        if name not in known:
            raise ValueError("unknown pinned ID")
        if fixed.setdefault(name, value) != value:
            conflict = True
    for i, bit in _pairs(occurrence_pins):
        if not 0 <= i < len(slots):
            raise ValueError("pinned occurrence outside physical key")
        name, offset = slots[i]
        value = bit ^ offset
        if fixed.setdefault(name, value) != value:
            conflict = True
    return fixed, conflict


def compile_pins(challenge, n, aliases, *, occurrence_pins=(), id_pins=()):
    """Return edges,start,final,events; contradictory valid pins give an empty chart."""
    slots = _slots(aliases, n)
    fixed, conflict = _fixed(slots, occurrence_pins, id_pins)
    edges, start, final, events = annotated_dag(challenge, n, aliases)
    if conflict:
        return [], 0, 1, {}
    outgoing = {}
    for j, (u, _, _) in enumerate(edges):
        outgoing.setdefault(u, []).append(j)
    forks = sorted(u for u, group in outgoing.items() if len(group) == 2)
    blocked = set()
    for u, (name, offset) in zip(forks, slots):
        if name in fixed:
            for j in outgoing[u]:
                if int(edges[j][1] == 45) != (fixed[name] ^ offset):
                    blocked.add(j)
    reachable = {start}
    keep = set()
    for u in sorted(outgoing):
        if u in reachable:
            for j in outgoing[u]:
                if j not in blocked:
                    keep.add(j)
                    reachable.add(edges[j][2])
    result = []
    annotations = {}
    for j, edge in enumerate(edges):
        if j in keep:
            if j in events:
                annotations[len(result)] = events[j]
            result.append(edge)
    return result, start, final, annotations


def complete_edge_prefix(edges, start, final, events, path):
    """Extend an edge-ID prefix of a compile_pins chart, retaining every original ID.

    Return None for an invalid prefix or empty chart. On charts from this module
    every alias-compatible prefix has a continuation: fixed values were applied
    to all occurrences, and each remaining return still offers both signs.
    """
    outgoing = {}
    for j, (u, _, _) in enumerate(edges):
        outgoing.setdefault(u, []).append(j)
    stack = []
    result = []
    here = start

    def advance(j):
        nonlocal here
        if type(j) is not int or not 0 <= j < len(edges) or edges[j][0] != here:
            return False
        if j in events:
            kind, name, value = events[j]
            if kind == "open":
                stack.append((name, value))
            elif kind == "close" and stack and stack[-1] == (name, value):
                stack.pop()
            else:
                return False
        here = edges[j][2]
        result.append(j)
        return True

    for j in path:
        if not advance(j):
            return None
    while here != final:
        for j in outgoing.get(here, ()):
            if advance(j):
                break
        else:
            return None
    if stack:
        return None
    parse(bytes(edges[j][1] for j in result))
    return result


def complete_prefix(challenge, n, aliases, chosen=(), *, occurrence_pins=(), id_pins=()):
    """Extend initial physical slot bits to canonical bytes; unused ID values default to zero.

    Return None for valid but inconsistent constraints. Invalid indices, malformed
    signed schedules, nonbinary entries and an oversized prefix raise ValueError.
    """
    annotated_dag(challenge, n, aliases)
    slots = _slots(aliases, n)
    chosen = tuple(chosen)
    if len(chosen) > len(slots):
        raise ValueError("too many physical prefix bits")
    pins = list(_pairs(occurrence_pins)) + list(enumerate(chosen))
    fixed, conflict = _fixed(slots, pins, id_pins)
    if conflict:
        return None
    expected = {name: fixed.get(name, 0) for name, _ in slots}
    key = sum((expected[name] ^ offset) << i for i, (name, offset) in enumerate(slots))
    raw = encode(challenge, n, key)
    rn, rc, rk, values = decode_alias(raw, aliases)
    if (rn != n or rc != [tuple(row) for row in challenge] or rk != key or values != expected):
        raise AssertionError("original physical completion failed replay")
    return raw
