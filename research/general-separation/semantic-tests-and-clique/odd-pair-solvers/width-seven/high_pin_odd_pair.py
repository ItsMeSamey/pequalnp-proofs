"""Find a minimal odd support with both pins nonleaf and induced maximum degree five.

Supply JSON with symmetric adjacency lists under neighbors and two indices under pins.
UNKNOWN refers to unrestricted existence.
"""
import argparse
from itertools import combinations
import json
import sys

from three_connected_odd_pair import adjacent, indexed_graph


def eligible(graph, sites):
    """Check the induced graph in the original host, with both pins first."""
    rows = [
        sum(1 << j for j, v in enumerate(sites) if adjacent(graph, u, v))
        for u in sites
    ]
    degrees = [r.bit_count() for r in rows]
    if min(degrees[:2]) < 3 or any(d not in (1, 3, 5) for d in degrees):
        return False
    full = (1 << len(sites)) - 1
    for mask in range(3, full, 4):
        if all((mask & row).bit_count() % 2 for j, row in enumerate(rows) if mask >> j & 1):
            return False
    return True


def find(lists, pins):
    graph = indexed_graph(lists)
    if (
        not isinstance(pins, (list, tuple))
        or len(pins) != 2
        or any(type(i) is not int or not 0 <= i < len(graph) for i in pins)
        or pins[0] == pins[1]
    ):
        raise ValueError("two distinct original vertex indices required")
    p, q = pins
    if adjacent(graph, p, q):
        return dict(high_pin_minimal=False, unrestricted="YES", witness=[p, q])
    near = set(graph[p]) | set(graph[q])
    ordered = sorted(near)
    for size in (4, 6):
        for group in combinations(ordered, size):
            sites = (p, q) + group
            if eligible(graph, sites):
                return dict(high_pin_minimal=True, unrestricted="YES", witness=list(sites))
    # Every single-leaf example has five near sites and one distance-two site.
    fringe = sorted({v for u in near for v in graph[u]} - near - {p, q})
    for group in combinations(ordered, 5):
        for v in fringe:
            sites = (p, q) + group + (v,)
            if eligible(graph, sites):
                return dict(high_pin_minimal=True, unrestricted="YES", witness=list(sites))
    return dict(high_pin_minimal=False, unrestricted="UNKNOWN", witness=None)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", nargs="?", type=argparse.FileType("r"), default=sys.stdin)
    args = parser.parse_args()
    instance = json.load(args.input)
    print(json.dumps(find(instance["neighbors"], instance["pins"])))


if __name__ == "__main__":
    main()
