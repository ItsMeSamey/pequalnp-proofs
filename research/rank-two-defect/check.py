"""Check the rank-two quadratic classification and its witness reductions."""
from itertools import permutations, product
from pathlib import Path
import runpy

alternating_witness = runpy.run_path(
    str(Path(__file__).resolve().parents[1] / "two-markers" / "check.py")
)["witness"]


def dot(a, b):
    return (a & b).bit_count() % 2


def update(rows, a, b):
    return tuple(row ^ (b if a >> i & 1 else 0) for i, row in enumerate(rows))


def classify(rows):
    n = len(rows)
    vectors = {row ^ sum(((rows[j] >> i) & 1) << j for j in range(n))
               for i, row in enumerate(rows)} - {0}
    if len(vectors) < 2:
        return None
    a, b = sorted(vectors)[:2]
    plane = {a, b, a ^ b}
    if not vectors <= plane:
        return None
    diagonal = sum((row >> i & 1) << i for i, row in enumerate(rows))
    for u, v in permutations(sorted(plane), 2):
        if diagonal == (u & v):
            return "hyperbolic", u, v
    if diagonal == (a ^ b ^ (a & b)):
        return "elliptic", a, b
    return "residual", a, b


def feasible(rows, x):
    return all(not (x >> i & 1) or not dot(row, x) for i, row in enumerate(rows))


def hyperbolic_witness(rows, h, a, b):
    for u, v in ((a, b), (b, a)):
        alternating = update(rows, u, v)
        labels = [(v >> i & 1) + 2 * (h >> i & 1) for i in range(len(rows))]
        candidate = alternating_witness(alternating, labels, 2)
        if candidate is not None:
            return candidate
    return None


def checks():
    counts = {}
    for n in range(1, 4):
        for rows in product(range(1 << n), repeat=n):
            result = classify(rows)
            if result is None:
                continue
            kind, a, b = result
            counts[kind] = counts.get(kind, 0) + 1
            actual = {x for x in range(1 << n) if feasible(rows, x)}
            if kind == "hyperbolic":
                for h in range(1 << n):
                    w = hyperbolic_witness(rows, h, a, b)
                    desired = {x for x in actual if dot(h, x)}
                    assert w in desired if desired else w is None
            if kind == "elliptic":
                alt = update(update(update(rows, a, b), a, a), b, b)
                assert all(not (row >> i & 1) for i, row in enumerate(alt))
                assert actual == {x for x in range(1 << n)
                                  if not dot(a, x) and not dot(b, x) and feasible(alt, x)}
    print(counts)


if __name__ == "__main__":
    checks()
