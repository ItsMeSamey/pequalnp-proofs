"""Exhaustive and seeded checks of the charge-basis packing and fixed-star loss."""

from itertools import combinations
from random import Random


def pack_interiors(interiors, rank, target_count):
    space = set(range(1 << rank))
    cover = set()
    while len(space) > 1:
        bases = []
        used = set()
        marked = set()
        for _ in range(target_count):
            span = {0}
            basis = []
            while span != space:
                for index, (charge, ports) in enumerate(interiors):
                    available = sorted(set(ports) - marked)
                    if index not in used and charge in space - span and len(available) >= 2:
                        break
                else:
                    cover.update(v for i in used for v in interiors[i][1])
                    space = span
                    break
                pair = tuple(available[:2])
                basis.append((index, pair))
                marked.update(pair)
                used.add(index)
                span |= {v ^ charge for v in span}
            else:
                bases.append(basis)
                continue
            break
        else:
            return space, cover, bases
    return space, cover, []


def check(interiors, rank, target_count):
    space, cover, bases = pack_interiors(interiors, rank, target_count)
    adhesion = max((len(ports) for _, ports in interiors), default=0)
    assert len(cover) <= adhesion * target_count * rank * (rank + 1) // 2
    if len(space) > 1:
        assert len(bases) == target_count
    indices = set()
    marks = set()
    for basis in bases:
        subset_sums = {0}
        for i, pair in basis:
            assert i not in indices
            indices.add(i)
            assert not (marks & set(pair))
            marks.update(pair)
            charge, ports = interiors[i]
            assert set(pair) <= set(ports) and len(set(pair)) == 2
            assert charge not in subset_sums
            subset_sums |= {v ^ charge for v in subset_sums}
        assert subset_sums == space
    for charge, ports in interiors:
        if charge in space:
            continue
        outside = set(ports) - cover
        assert len(outside) <= 1
        root = next(iter(outside), ports[0])
        assert all(x in cover and y in cover for x, y in combinations(ports, 2)
                   if root not in (x, y))


def main():
    candidates = [(charge, pts) for charge in range(1, 4)
                  for pts in [(0, 1), (0, 2), (1, 2), (0, 1, 2)]]
    for mask in range(1 << len(candidates)):
        interiors = [item for i, item in enumerate(candidates) if mask >> i & 1]
        for target_count in (1, 2):
            check(interiors, 2, target_count)
    rng = Random(7713)
    for _ in range(1000):
        size = rng.randrange(3, 36)
        rank = rng.randrange(1, 6)
        interiors = [(rng.randrange(1 << rank),
                      tuple(rng.sample(range(size), rng.randint(1, min(size, 5)))))
                     for _ in range(rng.randrange(80))]
        check(interiors, rank, rng.randrange(1, 6))
    print("Passed 8192 exhaustive rank-two cases and 1000 seeded cases.")


if __name__ == "__main__":
    main()
