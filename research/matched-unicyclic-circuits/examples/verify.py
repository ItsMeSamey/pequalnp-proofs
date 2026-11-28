"""Independent scalar and graph checks for the two named upper-bound fixtures."""
import json
from itertools import combinations, permutations
from pathlib import Path


def require(test, message):
    if not test:
        raise ValueError(message)


def check(name, attachment):
    data = json.loads(Path(__file__).with_name(name + ".json").read_text())
    edges = {tuple(sorted(e)) for e in data["edges"]}
    cycle = {tuple(sorted((i, (i + 1) % 6))) for i in range(6)}
    require(data["n"] == 8 and len(data["edges"]) == 8, "fixture size")
    require(edges == cycle | {(0, 6), (attachment, 7)}, "labeled graph")
    require(any(len(set(sum(match, ()))) == 8 for match in combinations(edges, 4)), "matching")
    require(not any(all(tuple(sorted((p[i], p[(i + 1) % 4]))) in edges for i in range(4))
                    for p in permutations(range(8), 4)), "four-cycle")
    gates = data["gates"]
    require(len(gates) == 11 and 0 <= data["output"] < 19, "circuit dimensions")
    for row in range(256):
        wires = [bool(row & (1 << k)) for k in range(8)]
        expected = any(wires[a] and wires[b] for a, b in edges)
        for op, a, b in gates:
            require(op in ("and", "or") and 0 <= a < len(wires) and 0 <= b < len(wires), "gate")
            wires.append((wires[a] and wires[b]) if op == "and" else (wires[a] or wires[b]))
        require(wires[data["output"]] == expected, (name, row))
    print(name, "verified 256 rows, matching, exact labeled cycle and leaves, 11 gates")


if __name__ == "__main__":
    check("adjacent", 1)
    check("opposite", 3)
