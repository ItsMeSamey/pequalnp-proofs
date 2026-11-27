"""Tiny exhaustive oracle for the one-block transfer."""
from itertools import product
from math import prod

from palette_transfer import block_transfer


def check():
    weights = [[2, -1, 3, 0], [1, 3, -2, 2], [1, -2, 1, 4], [2, 1, -1, 2]]
    labels = [[0, 1, 2, 3], [0, 2, 1, 3], [0, 3, 0, 3], [0, 1, 0, 1]]
    for pins in ({}, {0: 1}, {0: 1, 3: 2}, {0: 1, 3: 1}):
        expected = [0] * 4
        for colors in product(range(4), repeat=4):
            if set(colors[:2]) & set(colors[2:]):
                continue
            if any(colors[v] != c for v, c in pins.items()):
                continue
            label = 0
            for v, c in enumerate(colors):
                label ^= labels[v][c]
            expected[label] += prod(weights[v][c] for v, c in enumerate(colors))
        for target, count in enumerate(expected):
            for p in (None, 0, 1, 5):
                got = block_transfer(weights, labels, 2, target, pins=pins, precision=p)
                assert got == (count if p is None else count % (1 << p))
    print("palette transfer oracle passed")


if __name__ == "__main__":
    check()
