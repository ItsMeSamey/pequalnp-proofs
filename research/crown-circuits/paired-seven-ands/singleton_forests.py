"""Classify literal-only dirty continuations as unordered rooted binary-slot forests."""
from itertools import product
from collections import Counter


def forests(d):
    # Each dirty output feeds exactly one port of a chronologically later gate.
    found = {}
    for destinations in product(*(range(2*(j+1),14) for j in range(d))):
        children = [[[],[]] for _ in range(7)]
        for j, tap in enumerate(destinations):
            a, b = tap//2, tap%2
            shape = tuple(sorted(tuple(sorted(g)) for g in children[j]))
            children[a][b].append(shape)
        key = tuple(sorted(tuple(sorted(tuple(sorted(g)) for g in tree))
                           for tree in children[d:]))
        found.setdefault(key, destinations)
    return found


if __name__ == '__main__':
    for d in range(1,7):
        pool = forests(d)
        print(d, len(pool), flush=True)
