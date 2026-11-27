"""Independent chart enumeration and physical witness checks."""
import random
from itertools import product

from thick_tag_solver import solve


def trace(columns):
    span = {0}
    for v, h, t in columns:
        z = (v << 4) | (t << 2) | h
        span |= {p ^ z for p in span}
    return span & set(range(16))


def reference(columns, rank):
    for word in product(range(4), repeat=rank):
        colors = [0]
        for t in word:
            colors += [a ^ t for a in colors]
        if trace([c for c in columns if c[2] == colors[c[0]]]) == {0, 1, 2, 3}:
            return True
    return False


def run():
    rng = random.Random(4107)
    for iteration in range(1200):
        rank = rng.randrange(4)
        columns = []
        for _ in range(rng.randrange(13)):
            v, h = rng.randrange(1 << rank), rng.randrange(4)
            tags = rng.sample(range(4), rng.randrange(1, 5))
            columns.extend((v, h, t) for t in tags)
        rng.shuffle(columns)
        witness = solve(columns)
        assert (witness is not None) == reference(columns, rank), (iteration, columns)
        if witness is not None:
            assert len(witness) == len(set(witness))
            assert all(0 <= i < len(columns) for i in witness)
            assert trace([columns[i] for i in witness]) == {0, 1, 2, 3}
    print("1200 chart-oracle comparisons, all physical witnesses verified")


if __name__ == "__main__":
    run()
