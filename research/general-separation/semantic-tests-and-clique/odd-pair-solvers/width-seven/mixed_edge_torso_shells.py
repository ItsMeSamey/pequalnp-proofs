"""Enumerate mixed root shells. Diagonal at site zero implements its even target."""
from collections import Counter
from itertools import combinations
from degree_five_raw_shell_check import Raw, grow, ones
import degree_five_terminal_sweep as sweep


def exact(rows):
    full = (1 << len(rows)) - 1
    return all(row.bit_count() % 2 for row in rows) and not any(
        all((rows[i] & mask).bit_count() % 2 for i in ones(mask))
        for mask in range(3, full, 4))


def roots():
    pairs = list(combinations(range(2, 6), 2))
    for graph in range(1 << len(pairs)):
        rows = [1, 0, 0, 0, 0, 0]
        edges = [(0, 1)] + [(p, i) for i in (2, 3, 4) for p in (0, 1)] + [(1, 5)]
        for i, j in edges + [pair for h, pair in enumerate(pairs) if graph >> h & 1]:
            rows[i] |= 1 << j
            rows[j] |= 1 << i
        ports = [i for i in range(2, 6) if rows[i].bit_count() < 5]
        old = Raw(rows, ports, range(3, 64, 4))
        if len(ports) >= 3 and not old.ok[0]:
            yield old


if __name__ == '__main__':
    sweep.exact_word = exact
    # Search only for a positive physical control; keep the first prefix of each type.
    first = {state.key: state for state in roots()}
    second = {}
    for state in first.values():
        for child in grow(state):
            second.setdefault(child.key, child)
    for state in second.values():
        for rows in sweep.terminal(state):
            if len(rows) > 7:
                physical = (rows[0] ^ 1,) + rows[1:]
                from edge_torso_atlas_check import witnesses
                assert witnesses(physical, 0, 1) and sweep.three_connected(physical)
                print(len(first), len(second), physical)
                raise SystemExit(0)
    raise AssertionError("expected a larger mixed-parity control")
