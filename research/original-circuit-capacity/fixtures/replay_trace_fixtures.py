"""Replay the supplied physical signed-path fixtures using only Python's standard library."""
from pathlib import Path
import argparse
import hashlib
import json

FIXTURE_SHA = "6261971a06a065c7324826046e06894f9f23a5b089215d157ae97f8cf11b5da7"


def check_record(record):
    n = record["inputs"]
    gates = record["gates"]
    out = record["output"]
    donor = record["donor"]
    paths = [[(0, [])] if i == donor else [] for i in range(n)]
    for wire, (op, pins) in enumerate(gates, n):
        if op not in ("and", "or", "not") or any(type(p) is not int or p < 0 for p in pins):
            raise ValueError("invalid physical gate")
        occurrences = []
        for slot, source in enumerate(pins[:1] if op == "not" else pins):
            if source < wire:
                for odd, hops in paths[source]:
                    occurrences.append((odd ^ int(op == "not"), [[wire, slot]] + hops))
        paths.append(occurrences)
    observed = [dict(odd=odd, pins=hops) for odd, hops in (paths[out] if out < len(paths) else [])]
    if observed != record["donor_paths"]:
        raise ValueError(f"{record['name']}: path mismatch")
    truth = []
    for pattern in range(1 << n):
        values = [bool(pattern & (1 << i)) for i in range(n)]
        for op, pins in gates:
            operands = [values[i] if i < len(values) else False for i in pins]
            if op == "and":
                value = all(operands)
            elif op == "or":
                value = any(operands)
            else:
                value = not (operands[0] if operands else False)
            values.append(value)
        truth.append(int(values[out]) if out < len(values) else 0)
    if truth != record["truth_lsb_coordinate0"]:
        raise ValueError(f"{record['name']}: truth table mismatch")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("fixtures", type=Path)
    data = parser.parse_args().fixtures.read_bytes()
    if hashlib.sha256(data).hexdigest() != FIXTURE_SHA:
        raise ValueError("fixture digest mismatch")
    records = json.loads(data)
    for record in records:
        check_record(record)
    print(f"Verified truth tables and ordered signed pin paths for {len(records)} fixtures.")
