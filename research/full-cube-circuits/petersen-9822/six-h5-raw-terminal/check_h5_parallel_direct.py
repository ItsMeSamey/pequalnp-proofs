"""Independent direct census of four leaky raw products on the ten-variable graph."""
from collections import Counter, defaultdict
from itertools import combinations

from h5_raw_terminal import EDGES, target


def hit_signature(shore, rows):
    return sum(bool(shore & row) << i for i, row in enumerate(rows))


def census():
    maximal = [
        row for row in range(1024) if not target(row)
        and all(target(row | 1 << i) for i in range(10) if not row & (1 << i))
    ]
    assert len(maximal) == 16 and len(EDGES) == 13
    shores = [(hit_signature(s, maximal), hit_signature(s, EDGES)) for s in range(1, 1024)]
    masks = defaultdict(set)
    for leaks_a, edges_a in shores:
        for leaks_b, edges_b in shores:
            leaks = leaks_a & leaks_b
            if leaks:
                masks[leaks].add(edges_a & edges_b)
    print("Realized nonzero leak masks", len(masks))
    histogram = Counter()
    for i, j in combinations(range(16), 2):
        left, right = 1 << i, 1 << j
        assert all(leaks & ~(left | right) for leaks, _ in shores)
        candidates = set().union(*(masks.get(k, ()) for k in (left, right, left | right)))
        largest = [x for x in candidates if not any(x != y and not (x & ~y) for y in candidates)]
        reachable = {0}
        for _ in range(4):
            reachable |= {x | y for x in reachable for y in largest}
        histogram[max(mask.bit_count() for mask in reachable)] += 1
    return histogram


if __name__ == '__main__':
    observed = census()
    assert observed == {0: 105, 6: 2, 7: 8, 8: 5}
    print(sorted(observed.items()))
