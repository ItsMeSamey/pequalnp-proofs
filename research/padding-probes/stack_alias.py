"""Canonical physical DIMACS byte choices with signed, repeated alias IDs."""
from heapq import heappop, heappush

from padding_cnf import encode, parse


def _slots(aliases, n):
    if not isinstance(aliases, (list, tuple)) or len(aliases) != n + 1:
        raise ValueError("expected one alias per key slot, including enable")
    result = []
    for alias in aliases:
        if type(alias) is int and alias != 0:
            result.append((abs(alias), int(alias < 0)))
        elif isinstance(alias, (tuple, list)) and len(alias) == 2:
            variable, offset = alias
            if type(variable) is not int or variable < 1:
                raise ValueError("alias IDs must be positive integers")
            if type(offset) is not int or offset not in (0, 1):
                raise ValueError("alias offset must be integer 0 or 1")
            result.append((variable, offset))
        else:
            raise ValueError("expected a nonzero signed ID or an (ID, offset) pair")
    return result


def decode_alias(raw, aliases):
    """Check actual marker signs; return (n, challenge, physical_key, underlying_values)."""
    n, challenge, key = parse(raw)
    values = {}
    for i, (variable, offset) in enumerate(_slots(aliases, n)):
        value = ((key >> i) & 1) ^ offset
        if variable in values and values[variable] != value:
            raise ValueError("inconsistent physical key bits for a repeated alias")
        values[variable] = value
    return n, challenge, key, values


def alias_dag(challenge, n, aliases):
    """Return (edges, start, final) for stack_probe, with forward integer vertex IDs.

    A boundary state stores only IDs occurring on both sides. For encoded
    length L and maximum boundary width w, the graph has O(L 2^w) edges and
    vertices, including up to two complete physical slot paths per state.
    """
    zero_lines = encode(challenge, n, 0).splitlines(keepends=True)
    slots = _slots(aliases, n)
    one_lines = encode(challenge, n, (1 << (n + 1)) - 1).splitlines(keepends=True)
    prefix_count = len(zero_lines) - len(slots)
    last = {variable: i for i, (variable, _) in enumerate(slots)}
    edges = []
    current = 0
    for line in zero_lines[:prefix_count]:
        for byte in line:
            edges.append((current, byte, current + 1))
            current += 1
    frontier = {0: current}  # live value mask -> boundary vertex
    next_vertex = current + 1
    lanes = {}
    free_lanes = []
    lane_count = 0
    for i, (variable, offset) in enumerate(slots):
        spellings = (zero_lines[prefix_count + i], one_lines[prefix_count + i])
        existing = variable in lanes
        final_use = i == last[variable]
        if not existing and not final_use:
            if free_lanes:
                lanes[variable] = heappop(free_lanes)
            else:
                lanes[variable] = lane_count
                lane_count += 1
        lane_bit = 1 << lanes[variable] if variable in lanes else 0
        endings = []
        destinations = {}
        for mask, vertex in frontier.items():
            choices = (int(bool(mask & lane_bit)),) if existing else (0, 1)
            for value in choices:
                dest_mask = (mask & ~lane_bit) if final_use else (mask | (value * lane_bit))
                spelling = spellings[value ^ offset]
                source = vertex
                for byte in spelling[:-1]:
                    edges.append((source, byte, next_vertex))
                    source = next_vertex
                    next_vertex += 1
                endings.append((source, spelling[-1], dest_mask))
                destinations[dest_mask] = None
        frontier = {}
        for mask in destinations:
            frontier[mask] = next_vertex
            next_vertex += 1
        edges.extend((source, byte, frontier[mask]) for source, byte, mask in endings)
        if existing and final_use:
            heappush(free_lanes, lanes.pop(variable))
    return edges, 0, frontier[0]
