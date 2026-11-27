"""Replay integer lower and upper bounds for the positive rectangle cover."""
import hashlib
import json
import re
from pathlib import Path


def require(condition, message):
    if not condition:
        raise ValueError(message)


def load(directory, name):
    return json.loads((directory / name).read_text(encoding="utf-8"))


def maximal_rectangles(rows):
    # Each maximal column set is the intersection of its chosen rows.
    intersections = {(1 << 32) - 1}
    for row in rows:
        intersections.update({cols & row for cols in intersections})
    result = []
    for cols in intersections:
        if cols:
            row_mask = sum(1 << i for i, row in enumerate(rows) if row & cols == cols)
            if row_mask:
                result.append((row_mask, cols))
    return sorted(result)


def check(directory):
    raw = load(directory, "graph.json")
    require(isinstance(raw, list) and len(raw) == 32, "expected 32 rows")
    require(all(type(row) is str and re.fullmatch(r"0x[0-9a-fA-F]{8}", row)
                for row in raw), "invalid graph row")
    statement = (directory / "statement.txt").read_text(encoding="utf-8")
    require(re.findall(r"0x[0-9a-fA-F]{8}", statement) == raw, "statement and graph disagree")
    rows = [int(row, 16) for row in raw]
    rectangles = maximal_rectangles(rows)
    encoded = json.dumps(rectangles, separators=(",", ":")) + "\n"
    digest = hashlib.sha256(encoded.encode("ascii")).hexdigest()

    cert = load(directory, "rectangle_dual.json")
    require(type(cert) is dict and set(cert) == {
        "weights", "total", "denominator", "dictionary_sha256"
    }, "unexpected dual certificate fields")
    require(cert["dictionary_sha256"] == digest, "dictionary hash mismatch")
    weights = cert["weights"]
    edges = [(i, j) for i, row in enumerate(rows) for j in range(32) if row >> j & 1]
    require(type(weights) is list and len(weights) == len(edges), "invalid weight count")
    require(all(type(w) is int and w >= 0 for w in weights), "invalid edge weight")
    total = sum(weights)
    require(type(cert["total"]) is int and cert["total"] == total, "invalid weight sum")
    denominator = cert["denominator"]
    require(type(denominator) is int and denominator > 0, "invalid denominator")
    matrix = [[0] * 32 for _ in rows]
    for (i, j), weight in zip(edges, weights):
        matrix[i][j] = weight
    maximum = 0
    for row_mask, cols in rectangles:
        col_ids = [j for j in range(32) if cols >> j & 1]
        load_sum = sum(matrix[i][j] for i in range(32) if row_mask >> i & 1 for j in col_ids)
        require(load_sum <= denominator, "rectangle exceeds denominator")
        maximum = max(maximum, load_sum)
    require(maximum == denominator, "denominator differs from maximum rectangle weight")
    lower = (total + denominator - 1) // denominator

    cover = load(directory, "cover30.json")
    require(type(cover) is list and len(cover) == 30, "expected 30 rectangles")
    covered = [0] * 32
    for pair in cover:
        require(type(pair) is list and len(pair) == 2, "expected two rectangle masks")
        require(all(type(m) is int and 0 < m < 1 << 32 for m in pair), "invalid mask")
        row_mask, cols = pair
        for i in range(32):
            if row_mask >> i & 1:
                covered[i] |= cols
    require(covered == rows, "cover union differs from the target graph")
    require(lower == 28 and lower <= len(cover), "claimed bounds not established")
    print(f"{len(edges)} edges; {len(rectangles)} maximal rectangles; total {total}; denominator {denominator}")
    print(f"{lower} <= positive rectangle cover number <= {len(cover)}")


if __name__ == "__main__":
    try:
        check(Path(__file__).resolve().parent)
    except (OSError, ValueError) as error:
        raise SystemExit(f"verification failed: {error}") from error
