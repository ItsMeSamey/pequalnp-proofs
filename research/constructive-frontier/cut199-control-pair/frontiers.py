"""Measure the 4186 defect and dirty-OR frontiers. All gate indices are zero-based."""
import argparse
import json
from pathlib import Path

from check4186 import check


def measure(candidate):
    edges = candidate["edges"]
    if "n" in candidate:
        n = candidate["n"]
    else:
        # Both cut199 control files omit n. Other graphs may have isolated vertices.
        cut199 = {(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10),
                  (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9),
                  (6, 7), (6, 10), (7, 9), (8, 9)}
        if {tuple(sorted(edge)) for edge in edges} != cut199:
            raise ValueError("supply n explicitly for graphs other than the cut199 controls")
        n = 11

    gates = []
    for gate in candidate["gates"]:
        if isinstance(gate, dict):
            op = gate["op"]
            a, b = gate["inputs"]
        else:
            op, a, b = gate
        if isinstance(op, bool):
            op = "and" if op else "or"
        gates.append((op, a, b))

    audit = check(n, edges, gates, candidate["output"])
    clean = set(audit["belowF"])
    and_gates = audit["tops"] + audit["junk"]
    frontiers = []
    for g in audit["orN"]:
        clean_inputs = sorted({wire - n for wire in gates[g][1:] if wire - n in clean})
        descendants = [h for h in and_gates if g in audit["inCone"][h]]
        if clean_inputs and descendants:
            frontiers.append(dict(gate=g, clean_input_gates=clean_inputs,
                                  strict_and_descendants=sorted(descendants)))
    defect = audit["lhs"] - audit["rhs"]
    count = len(frontiers)
    return dict(computes=audit["computes"], topForm=audit["topForm"], D=defect,
                k=count, D_plus_k=defect + count, frontiers=frontiers)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("candidates", nargs="+", type=Path)
    for path in parser.parse_args().candidates:
        print(json.dumps({"path": str(path), **measure(json.loads(path.read_text()))}))
