"""Find a three-connected inclusion-minimal two-pin odd support of degree at most five.

Run with a JSON object containing 'neighbors' (lists indexed from zero) and
'pins' (two distinct original indices). UNKNOWN describes unrestricted existence.
"""

import argparse
from bisect import bisect_left
from itertools import combinations
import json
import sys


def adjacent(neighbors, a, b):
    row = neighbors[a]
    pos = bisect_left(row, b)
    return pos < len(row) and row[pos] == b


def indexed_graph(lists):
    n = len(lists)
    rows = []
    for i, source in enumerate(lists):
        if any(type(v) is not int or not 0 <= v < n or v == i for v in source):
            raise ValueError("invalid neighbor in row %d" % i)
        row = tuple(sorted(source))
        if any(a == b for a, b in zip(row, row[1:])):
            raise ValueError("duplicate neighbor in row %d" % i)
        rows.append(row)
    if any(not adjacent(rows, j, i) for i, row in enumerate(rows) for j in row):
        raise ValueError("asymmetric adjacency lists")
    return rows


def eligible(neighbors, sites):
    """Run only native tests on these actual sites, with the two pins first."""
    n = len(sites)
    full = (1 << n) - 1
    rows = [
        sum(1 << j for j, v in enumerate(sites) if adjacent(neighbors, u, v))
        for u in sites
    ]
    if any(row.bit_count() not in (3, 5) for row in rows):
        return False
    for i, j in combinations(range(n), 2):
        live = full ^ (1 << i) ^ (1 << j)
        reached = live & -live
        pending = reached
        while pending:
            bit = pending & -pending
            pending ^= bit
            fresh = live & rows[bit.bit_length() - 1] & ~reached
            reached |= fresh
            pending |= fresh
        if reached != live:
            return False
    for mask in range(3, full, 4):
        if all(
            (row & mask).bit_count() % 2 for j, row in enumerate(rows) if mask >> j & 1
        ):
            return False
    return True


def find(lists, pins):
    neighbors = indexed_graph(lists)
    n = len(neighbors)
    if (
        len(pins) != 2
        or any(type(i) is not int or not 0 <= i < n for i in pins)
        or pins[0] == pins[1]
    ):
        raise ValueError("two distinct original vertex indices required")
    p, q = pins
    # The theorem requires that all witness sites lie in these two neighborhoods.
    pool = sorted((set(neighbors[p]) | set(neighbors[q])) - {p, q})
    if not adjacent(neighbors, p, q):
        for size in (4, 6):
            for extra in combinations(pool, size):
                candidate = (p, q) + extra
                if eligible(neighbors, candidate):
                    return dict(
                        three_connected_minimal=True,
                        unrestricted="YES",
                        witness=list(candidate),
                    )
    return dict(three_connected_minimal=False, unrestricted="UNKNOWN", witness=None)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "input", nargs="?", type=argparse.FileType("r"), default=sys.stdin
    )
    args = parser.parse_args()
    instance = json.load(args.input)
    print(json.dumps(find(instance["neighbors"], instance["pins"])))


if __name__ == "__main__":
    main()
