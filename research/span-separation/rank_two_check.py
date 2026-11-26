"""Compare each intersection dimension against its own rooted circuit test."""
from itertools import combinations
from random import Random


def subsets(seq):
    return (x for size in range(len(seq) + 1) for x in combinations(seq, size))


def rank(cols):
    pivots = {}
    for x in cols:
        while x and x.bit_length() in pivots:
            x ^= pivots[x.bit_length()]
        if x:
            pivots[x.bit_length()] = x
    return len(pivots)


def circuits_with_triple(cols, terminals, dual=False):
    """Use dual rank directly to test circuit minimality, preserving ground indices."""
    n = len(cols)
    whole = range(n)
    full_rank = rank(cols)
    def get_rank(indices):
        if dual:
            return len(indices) - full_rank + rank(cols[i] for i in whole if i not in indices)
        return rank(cols[i] for i in indices)
    for add in subsets(range(n - 3)):
        sel = frozenset((*terminals, *add))
        if get_rank(sel) == len(sel) - 1 and all(get_rank(sel - {i}) == len(sel) - 1 for i in sel):
            return True
    return False


def check(ground, u, v, w):
    found = [False, False]
    for x in subsets(ground):
        r = rank(x)
        if rank((*x, u)) != r or rank((*x, u, v, w)) == rank((*x, u, v)):
            continue
        found[rank((*x, v)) == r] = True
    terminal_indices = range(len(ground), len(ground) + 3)
    one = circuits_with_triple((*ground, v, w, u ^ v ^ w), terminal_indices)
    two = circuits_with_triple((*ground, w, w ^ u, w ^ v), terminal_indices, dual=True)
    assert [one, two] == found, (ground, u, v, w, found, one, two)


def all_traces(ground, basis):
    def span(vectors):
        result = {0}
        for y in vectors:
            result |= {z ^ y for z in result}
        return frozenset(result)
    interface = span(basis)
    actual = {span(x) & interface for x in subsets(ground)}
    roots = range(len(ground), len(ground) + 3)
    predicted = {frozenset({0})}
    if interface <= span(ground):
        predicted.add(interface)
    for t in sorted(interface - {0}):
        a, b = next((a, b) for a, b in combinations(sorted(interface), 2)
                    if rank([t, a, b]) == 3)
        if circuits_with_triple((*ground, a, b, a ^ b ^ t), roots):
            predicted.add(span([t]))
    planes = {span(pair) for pair in combinations(sorted(interface - {0}), 2)}
    for plane in planes:
        a, b = sorted(plane - {0})[:2]
        c = min(interface - plane)
        if circuits_with_triple((*ground, c, c ^ a, c ^ b), roots, dual=True):
            predicted.add(plane)
    assert actual == predicted, (ground, basis, actual, predicted)


if __name__ == "__main__":
    count = 0
    for e in subsets(range(1, 8)):
        check(e, 1, 2, 4)
        all_traces(e, (1, 2, 4))
        count += 1
    rng = Random(173)
    for i in range(600):
        d = rng.randrange(3, 9)
        while True:
            u, v, w = (rng.randrange(1, 2**d) for _ in range(3))
            if rank((u, v, w)) == 3:
                break
        ground = tuple(rng.randrange(2**d) for _ in range(rng.randrange(1, 10)))
        check(ground, u, v, w)
        if i < 50:
            all_traces(ground, (u, v, w))
        count += 1
    print(f"Both branch checks agree on {count} instances; all 16 traces agree on 178.")
