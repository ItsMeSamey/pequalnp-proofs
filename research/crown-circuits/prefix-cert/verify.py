"""Check the fixed 29-gate prefix certificate with Python 3.10 or later."""

from functools import cache
from hashlib import sha256
from itertools import combinations
from pathlib import Path

LABELS = 12
RAW_WIRES = 2 * LABELS
PREFIX_GATES = 29
WIRES = RAW_WIRES + PREFIX_GATES
MAX_SOURCES = 12
SHARED = 1 << WIRES
PREFIX_SHA256 = "4a1f23a162d0c5aecc2ac98939286ac2d4f7db292f1ed91bdc47e3a155c942fd"


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


def split_rejections(positive, negative, support):
    """Count inner and outer obstructions for all nonempty proper subsets."""
    inside = outside = 0
    inner = (support - 1) & support
    while inner:
        outer = support ^ inner
        forced = [(p, n) for p in positive for n in negative if not (p & ~n & outer)]
        true_values = {p & inner for p, _ in forced}
        false_values = {n & inner for _, n in forced}
        if not rectangles_possible(true_values, false_values, inner):
            inside += 1
        else:
            can_be_true = {p for p in positive
                           if all((p & inner) & ~v for v in false_values)}
            can_be_false = {n for n in negative
                            if all(v & ~(n & inner) for v in true_values)}

            def shared_ok(p, n):
                return p in can_be_true and n in can_be_false and bool(p & ~n & inner)

            require(not rectangles_possible(positive, negative, outer, shared_ok),
                    f"Unexcluded shared subcircuit on mask {inner} of {support}")
            outside += 1
        inner = (inner - 1) & support
    return inside, outside


def main():
    prefix = Path(__file__).with_name("prefix.txt").read_bytes()
    require(sha256(prefix).hexdigest() == PREFIX_SHA256, "Unexpected prefix contents")
    gates = [tuple(map(int, line.split())) for line in prefix.splitlines()]
    positive, negative = truth_tables(gates)
    cuts = separation_cuts(positive, negative)
    require(len(cuts) == 42, "Unexpected separation-cut count")
    supports = source_sets(cuts)
    census = {size: len(masks) for size, masks in supports.items() if masks}
    require(census == {11: 2, 12: 118}, f"Unexpected support counts {census}")

    read_once = 0
    splits = {}
    for size in census:
        for mask in sorted(supports[size]):
            pos = extremal_values({p & mask for p in positive}, minimal=True)
            neg = extremal_values({n & mask for n in negative}, minimal=False)
            require(not rectangles_possible(pos, neg, mask), f"Read-once survivor {mask}")
            read_once += 1
            if size == 11:
                splits[mask] = split_rejections(pos, neg, mask)

    expected = {6755460627562496: (2026, 20), 6966566709100544: (1957, 89)}
    require(read_once == 120 and splits == expected, "Unexpected rectangle counts")
    print(f"Verified {len(cuts)} cuts and {read_once} read-once exclusions")
    for mask, (inside, outside) in splits.items():
        print(f"Support {mask}: {inside} inner and {outside} outer exclusions")
    print("No monotone binary suffix of at most 11 gates completes this prefix.")


if __name__ == "__main__":
    main()
