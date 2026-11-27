"""Compare common-coordinate-plane recognition with exhaustive GF(2) bases."""
from itertools import combinations, permutations
from random import Random


def rank(words):
    pivots = {}
    for word in words:
        while word:
            j = word.bit_length()
            if j not in pivots:
                pivots[j] = word
                break
            word ^= pivots[j]
    return len(pivots)


def recognize(planes):
    """Planes are sets of their three nonzero vectors. Reject malformed input."""
    if len(set(planes)) != len(planes):
        raise ValueError("duplicate plane")
    for plane in planes:
        if len(plane) != 3 or min(plane) <= 0 or rank(plane) != 2:
            raise ValueError("expected nonzero vectors of a binary plane")
    forced = set()
    for u, v in combinations(planes, 2):
        forced.update(u & v)
    if rank(forced) != len(forced):
        return False
    private = 0
    for plane in planes:
        common = len(plane & forced)
        if common > 2:
            return False
        private += 2 - common
    return rank(x for plane in planes for x in plane) == len(forced) + private


def verify(n, rng):
    vectors = range(1, 1 << n)
    planes = sorted({frozenset((a, b, a ^ b)) for a, b in combinations(vectors, 2)},
                    key=lambda p: tuple(sorted(p)))
    index = {p: i for i, p in enumerate(planes)}
    # Every listed family is a subset of the coordinate pairs of some ordered basis.
    possible = set()
    bases = 0
    for basis in permutations(vectors, n):
        if rank(basis) != n:
            continue
        bases += 1
        if tuple(sorted(basis)) != basis:
            continue  # All orderings induce the same set of pairs.
        mask = 0
        for a, b in combinations(basis, 2):
            mask |= 1 << index[frozenset((a, b, a ^ b))]
        sub = mask
        while True:
            possible.add(sub)
            if sub == 0:
                break
            sub = (sub - 1) & mask
    if n <= 3:
        tested = set(range(1 << len(planes)))
    else:
        tested = possible.copy()
        for k in range(5):
            for ids in combinations(range(len(planes)), k):
                tested.add(sum(1 << i for i in ids))
        for _ in range(1500):
            ids = rng.sample(range(len(planes)), rng.randrange(len(planes) + 1))
            tested.add(sum(1 << i for i in ids))
    for family in tested:
        chosen = [p for i, p in enumerate(planes) if family >> i & 1]
        assert recognize(chosen) == (family in possible)
    print(n, "dimension;", bases, "ordered bases;", len(possible), "positive families;",
          len(tested), "families checked")


if __name__ == "__main__":
    rng = Random(730)
    for dimension in range(5):
        verify(dimension, rng)
    star = [frozenset((1, v, 1 ^ v)) for v in (2, 4, 6)]
    assert not recognize(star)
    assert all(recognize(list(pair)) for pair in combinations(star, 2))
    print("three-plane star rejected; every proper subfamily accepted")
