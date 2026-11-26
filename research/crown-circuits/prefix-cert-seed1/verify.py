"""Verify the fixed prefix using Python 3.10 or later and a C++17 compiler."""

from functools import cache
from hashlib import sha256
from itertools import combinations
from pathlib import Path
import subprocess
import tempfile

LABELS = 12
RAW_WIRES = 2 * LABELS
PREFIX_GATES = 29
WIRES = RAW_WIRES + PREFIX_GATES
MAX_SOURCES = 12
SHARED = 1 << WIRES
PREFIX_SHA256 = "5ca60c19cf3953852881b9ebdc168623a2053452095d3523e471e63f5aeb386a"


def require(condition, message):
    if not condition:
        raise ValueError(message)


def bits(mask):
    """Yield individual one-bit masks in increasing order."""
    while mask:
        bit = mask & -mask
        yield bit
        mask ^= bit


def truth_tables(gates):
    require(len(gates) == PREFIX_GATES, "Expected exactly 29 prefix gates")
    inputs = [(row, col) for row in range(LABELS) for col in range(LABELS)]
    wires = [{pair for pair in inputs if wire in (pair[0], LABELS + pair[1])}
             for wire in range(RAW_WIRES)]
    for op, left, right in gates:
        require(op in (0, 1) and 0 <= left < len(wires) and 0 <= right < len(wires),
                "Invalid gate operation or predecessor")
        a, b = wires[left], wires[right]
        wires.append(a & b if op else a | b)
    positive, negative = [], []
    for pair in inputs:
        value = sum(1 << i for i, wire in enumerate(wires) if pair in wire)
        (negative if pair[0] == pair[1] else positive).append(value)
    return positive, negative


def separation_cuts(positive, negative):
    cuts = []
    differences = {p & ~n for p in positive for n in negative}
    for mask in sorted(differences, key=lambda x: (x.bit_count(), x)):
        if all(cut & ~mask for cut in cuts):
            cuts.append(mask)
    return cuts


def source_sets(cuts):
    """Find all hitting sets of size at most 12, including redundant supersets."""
    complete = set()

    @cache
    def visit(mask):
        remaining = [cut for cut in cuts if not cut & mask]
        if not remaining:
            complete.add(mask)
            return
        # Pairwise-disjoint unhit cuts require distinct additional sources.
        occupied = 0
        lower = mask.bit_count()
        for cut in remaining:
            if not cut & occupied:
                occupied |= cut
                lower += 1
        if lower > MAX_SOURCES:
            return
        for bit in bits(remaining[0]):
            visit(mask | bit)

    visit(0)
    supports = {size: set() for size in range(MAX_SOURCES + 1)}
    for mask in complete:
        unused = list(bits(((1 << WIRES) - 1) ^ mask))
        size = mask.bit_count()
        for extra in range(MAX_SOURCES - size + 1):
            for extension in combinations(unused, extra):
                supports[size + extra].add(mask | sum(extension))
    return supports


def extremal_values(values, minimal):
    return {v for v in values if not any(
        (u & ~v == 0 if minimal else v & ~u == 0) for u in values if u != v
    )}


def rectangles_possible(positive, negative, unique, shared_ok=None):
    """Force every singleton-choice cell's color on its rectangle hull."""
    cells = {(i, j): (p & ~n & unique)
             | (SHARED if shared_ok and shared_ok(p, n) else 0)
             for i, p in enumerate(positive) for j, n in enumerate(negative)}
    if 0 in cells.values():
        return False
    while True:
        changed = False
        for bit in bits(unique):
            forced = [cell for cell, choices in cells.items() if choices == bit]
            rows = {i for i, _ in forced}
            cols = {j for _, j in forced}
            for i in rows:
                for j in cols:
                    options = cells[i, j]
                    if not options & bit:
                        return False
                    if options != bit:
                        cells[i, j] = bit
                        changed = True
        if not changed:
            return True


def main():
    directory = Path(__file__).resolve().parent
    prefix = directory / "prefix.txt"
    data = prefix.read_bytes()
    require(sha256(data).hexdigest() == PREFIX_SHA256, "Unexpected prefix contents")
    gates = [tuple(map(int, line.split())) for line in data.splitlines()]
    positive, negative = truth_tables(gates)
    cuts = separation_cuts(positive, negative)
    require(len(cuts) == 50, f"Unexpected cut count {len(cuts)}")
    supports = source_sets(cuts)
    census = {size: len(masks) for size, masks in supports.items() if masks}
    require(census == {10: 2, 11: 109, 12: 2868}, f"Unexpected support counts {census}")

    for mask in supports[12]:
        pos = extremal_values({p & mask for p in positive}, minimal=True)
        neg = extremal_values({n & mask for n in negative}, minimal=False)
        require(not rectangles_possible(pos, neg, mask), f"Read-once survivor {mask}")
    print(f"Verified 50 cuts and {len(supports[12])} read-once exclusions.", flush=True)

    with tempfile.TemporaryDirectory() as scratch:
        executable = Path(scratch) / "token-search"
        subprocess.run(["c++", "-std=c++17", "-O3", str(directory / "token_search.cpp"),
                        "-o", str(executable)], check=True)
        for size in (10, 11):
            lines = [" ".join(str(bit.bit_length() - 1) for bit in bits(mask))
                     for mask in sorted(supports[size])]
            result = subprocess.run([str(executable), str(prefix)], input="\n".join(lines) + "\n",
                                    capture_output=True, text=True, check=True)
            require(result.stdout.strip() == str(len(lines)),
                    f"Unexpected completion count {result.stdout!r}")
            print(f"Exhausted all token merges for {len(lines)} supports of size {size}.", flush=True)
    print("No monotone binary suffix of at most 11 gates completes this prefix.")


if __name__ == "__main__":
    main()
