"""Verify the fixed prefix using Python 3.10 or later and a C++20 compiler."""

from functools import cache
from hashlib import sha256
from itertools import combinations
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
import argparse
import subprocess
import tempfile

LABELS = 12
RAW_WIRES = 2 * LABELS
PREFIX_GATES = 29
WIRES = RAW_WIRES + PREFIX_GATES
MAX_SOURCES = 12
NORMALIZED = ((1 << WIRES) - 1) ^ ((1 << RAW_WIRES) - 1)
PREFIX_SHA256 = "2ef549ef64c4dd0c4f12f457f117b03b924846a4b5a2e82ba479c2ece67d1c00"


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
    """Find all hitting sets of size at most twelve, including redundant supersets."""
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
        unused = list(bits(NORMALIZED & ~mask))
        size = mask.bit_count()
        for extra in range(MAX_SOURCES - size + 1):
            for extension in combinations(unused, extra):
                supports[size + extra].add(mask | sum(extension))
    return supports


def search_batch(executable, prefix, masks):
    rows = [" ".join(str(bit.bit_length() - 1) for bit in bits(mask)) for mask in masks]
    result = subprocess.run([executable, prefix], input="\n".join(rows) + "\n",
                            text=True, capture_output=True)
    require(result.returncode == 0 and result.stdout.strip() == str(len(rows)),
            f"Token check failed for batch starting with {rows[0]}: {result.stderr}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--jobs", type=int, default=3, help="Concurrent token-search batches")
    args = parser.parse_args()
    require(args.jobs > 0, "Expected at least one worker")
    directory = Path(__file__).resolve().parent
    prefix = directory / "prefix.txt"
    data = prefix.read_bytes()
    require(sha256(data).hexdigest() == PREFIX_SHA256, "Unexpected prefix")
    gates = [tuple(map(int, line.split())) for line in data.splitlines()]
    positive, negative = truth_tables(gates)
    for i in range(RAW_WIRES):
        pair = RAW_WIRES + i % LABELS
        require(all(not (p >> i & 1) or (p >> pair & 1) for p in positive)
                and all(not (n >> pair & 1) or (n >> i & 1) for n in negative),
                f"Invalid raw-wire substitution {i}")
    cuts = separation_cuts([v & NORMALIZED for v in positive], [v & NORMALIZED for v in negative])
    require(len(cuts) == 24, "Unexpected distinguishing constraints")
    supports = source_sets(cuts)
    census = {size: len(masks) for size, masks in supports.items() if masks}
    require(census == {7: 1, 8: 30, 9: 432, 10: 3929, 11: 25079, 12: 118267},
            f"Unexpected palette counts {census}")
    print("Normalized source palettes", census, flush=True)
    with tempfile.TemporaryDirectory() as temp:
        work = Path(temp)
        for name in ["canon", "split", "token_search"]:
            subprocess.run(["c++", "-std=c++20", "-O3", str(directory / f"{name}.cpp"),
                            "-o", str(work / name)], check=True)
        for size in census:
            masks = sorted(supports[size])
            if size < MAX_SOURCES:
                source = work / f"masks-{size}"
                representatives = work / f"classes-{size}"
                source.write_text("".join(f"{m}\n" for m in masks))
                subprocess.run([work / "canon", prefix, source, representatives], check=True)
                masks = list(map(int, representatives.read_text().splitlines()))
                if size == 10:
                    require(len(masks) == 557, "Unexpected ten-source class count")
                if size == 11:
                    require(len(masks) == 3540, "Unexpected eleven-source class count")
                    survivors = work / "shared-survivors"
                    subprocess.run([work / "split", prefix, representatives, survivors], check=True)
                    require(not survivors.read_text(), "One-reuse rectangle survivor")
                    print(f"Excluded {len(masks)} eleven-source classes", flush=True)
                    continue
            batch_size = 256 if size == 12 else 4
            batches = [masks[i:i + batch_size] for i in range(0, len(masks), batch_size)]
            with ThreadPoolExecutor(max_workers=args.jobs) as workers:
                for _ in workers.map(lambda batch: search_batch(work / "token_search", prefix, batch),
                                     batches):
                    pass
            print(f"Excluded {len(masks)} cases with {size} sources", flush=True)
    print("No binary monotone suffix of at most eleven gates completes this fixed grid prefix.")


if __name__ == "__main__":
    main()
