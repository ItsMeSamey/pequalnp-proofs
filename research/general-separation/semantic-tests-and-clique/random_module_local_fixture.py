"""Check four-guard directness modulo pin equations in two physical blowups."""
from itertools import combinations, product
from random import Random


BASE_ROWS = (
    (170, 449, 240, 81, 300, 341, 174, 327, 178),
    (170, 449, 240, 97, 356, 477, 446, 359, 242),
)


def check(base, t=32):
    rng = Random(3309)
    # Free vertices are indexed by module then position in the module.
    blocks = [((1 << t) - 1) << (t * j) for j in range(6)]

    def lift(old):
        return sum(block for j, block in enumerate(blocks) if old >> (j + 3) & 1)

    pin_span = [0]
    for row in base[:3]:
        pin_span += [u ^ lift(row) for u in pin_span]
    assert len(set(pin_span)) == 8
    rows = [lift(row) for row in base[3:] for _ in range(t)]
    for block in range(6):
        for i, j in combinations(range(block*t, (block+1)*t), 2):
            if rng.randrange(2):
                rows[i] ^= 1 << j
                rows[j] ^= 1 << i
    groups = []
    for i, row in enumerate(rows):
        unit = 1 << i
        choices = tuple(min(x ^ u for u in pin_span) for x in (unit, row, unit^row))
        assert len(set(choices)) == 3 and 0 not in choices
        groups.append(choices)
    # Canonical coset representatives (minimum integer) form a linear space.
    seen = {0: [0]}
    for size in (1, 2):
        for ids in combinations(range(len(groups)), size):
            sites = sum(1 << i for i in ids)
            for vals in product(*(groups[i] for i in ids)):
                value = vals[0] if size == 1 else vals[0] ^ vals[1]
                assert all(sites & prev for prev in seen.get(value, ()))
                seen.setdefault(value, []).append(sites)
    witnesses = [x for x in range(7, 512, 8)
                 if all(not (x >> i & 1) or not ((row & x).bit_count() % 2)
                        for i, row in enumerate(base))]
    return witnesses


if __name__ == "__main__":
    assert check(BASE_ROWS[0]) == []
    assert check(BASE_ROWS[1]) == [95, 175]
    print("Both six-module graphs pass all four-guard tests modulo rank-three pins.")
