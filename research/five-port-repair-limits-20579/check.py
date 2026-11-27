"""Replay the flat signed normal-form certificates for the frozen interface."""
import json
import re
import sys
from itertools import combinations
from pathlib import Path

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
from interface import reconstruct


def require(condition, message):
    if not condition:
        raise ValueError(message)


def read(name):
    return json.loads((HERE / name).read_text(encoding="utf-8"))


def signatures(values, count):
    require(type(values) is list and len(values) == count, "wrong signature count")
    require(all(type(v) is int and 0 <= v < 1 << 26 for v in values), "invalid signature")
    result = set(values)
    require(len(result) == count, "duplicate signatures")
    return result


def consistent(a, b, witness):
    return ((a ^ witness) & ~(a ^ b)) == 0


def main():
    graph = read("graph.json")
    require(type(graph) is list and len(graph) == 32 and all(
        type(row) is str and re.fullmatch(r"0x[0-9a-fA-F]{8}", row) for row in graph),
        "invalid graph words")
    rows = [int(row, 16) for row in graph]
    statement = HERE / "statement.txt"
    words = re.findall(r"\b0x[0-9a-fA-F]+\b", statement.read_text(encoding="utf-8"))
    require([int(w, 16) for w in words] == rows, "statement graph mismatch")
    context = read("context.json")
    bank = context["bank"]
    require(type(bank) is list and len(bank) == 26 and len(set(bank)) == 26 and
            all(type(w) is int and w > 0 for w in bank), "invalid interface bank")
    pos, neg = reconstruct(context, rows)
    care = read("care.json")
    require(signatures(care["positive"], 92) == pos and
            signatures(care["negative"], 427) == neg and not pos & neg,
            "care sets differ from reconstruction")
    bit = {w: 1 << i for i, w in enumerate(bank)}
    terms = read("terms.json")
    require(type(terms) is list and len(terms) == 58, "expected 58 terms")
    covered = set()
    for term in terms:
        require(type(term) is list and term and all(type(w) is int and abs(w) in bit
                for w in term), "invalid signed term")
        require(len(set(map(abs, term))) == len(term), "repeated variable in term")
        on = sum(bit[w] for w in term if w > 0)
        off = sum(bit[-w] for w in term if w < 0)
        def accepts(s):
            return s & on == on and s & off == 0
        require(not any(accepts(s) for s in neg), "term accepts a negative")
        covered.update(s for s in pos if accepts(s))
    require(covered == pos, "uncovered positive")

    cert = read("positive-blockers.json")
    require(cert["bank"] == bank, "positive blocker bank differs")
    vertices = cert["positive_signatures"]
    require(signatures(vertices, 58) <= pos, "clique outside positive set")
    witnesses = cert["negative_witnesses_in_pair_order"]
    require(type(witnesses) is list and len(witnesses) == 1653, "wrong blocker count")
    for (a, b), w in zip(combinations(vertices, 2), witnesses):
        require(type(w) is int and w in neg and consistent(a, b, w), "invalid negative blocker")

    patterns = read("negative-clique.json")["patterns"]
    require(type(patterns) is list and all(type(v) is str and
            re.fullmatch(r"0x[0-9a-fA-F]+", v) for v in patterns), "invalid clique encoding")
    vertices = [int(v, 16) for v in patterns]
    require(signatures(vertices, 25) <= neg, "clique outside negative set")
    pairs = 0
    for a, b in combinations(vertices, 2):
        require(any(consistent(a, b, p) for p in pos), "unblocked negative pair")
        pairs += 1
    units = 0
    for w in vertices:
        for i in range(len(bank)):
            require(any(((p ^ w) >> i) & 1 == 0 for p in pos), "unblocked unit clause")
            units += 1
    require((pairs, units) == (300, 650), "test count mismatch")
    # Each selected negative requires a different nonunit clause. Each clause
    # contributes at least one OR and combining them requires at least 24 ANDs
    # for the top conjunction. Distinct nonunit clause roots suffice for the OR count.
    print("Signed DNF minimum: 58 terms (1653 positive pairs checked)")
    print("Signed CNF lower bounds: 25 clauses, 49 binary gates in a flat formula")
    print(f"Checked {pairs} negative pairs and {units} unit-clause obstructions")
    from geometry import geometry
    from parents import parent_covers
    from private import audit_private
    residual, free = geometry(context, rows)
    covers = parent_covers(rows, residual, read("packing.json"))
    histogram = audit_private(covers, residual, free)
    require(histogram == read("private-histogram.json"), "paired-product histogram mismatch")
    require(len(covers) == 214 and sum(histogram.values()) == 202230 and
            histogram["overlap"] == 196530, "wrong parent or pairing counts")
    minimum = min(int(k) for k, count in histogram.items() if k != "overlap" and count)
    require(minimum == 28, "wrong private-OR lower bound")
    print("Paired products: 214 parent covers, 202230 pairings, "
          "at least 28 extra OR gates and 174 gates in total")



if __name__ == "__main__":
    try:
        main()
    except (OSError, KeyError, TypeError, ValueError) as error:
        raise SystemExit(f"verification failed: {error}") from error
