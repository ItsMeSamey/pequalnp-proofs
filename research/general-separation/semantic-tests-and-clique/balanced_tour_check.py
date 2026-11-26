"""Exact finite checks for the balanced rectangle and guard examples."""
from itertools import permutations, product
from math import comb, factorial


def count_three_blocks(m):
    return factorial(m)**3 * sum(comb(m, t)**3 for t in range(m + 1))


def single_cycle(p):
    seen = set()
    i = 0
    while i not in seen:
        seen.add(i)
        i = p[i]
    return len(seen) == len(p) and i == 0


def check_hybrids(n):
    arcs = list(product(range(n), repeat=2))
    cycles = {sum(1 << (i*n+j) for i, j in enumerate(p))
              for p in permutations(range(n)) if single_cycle(p)}
    def endpoints(mask):
        active = [arc for j, arc in enumerate(arcs) if mask >> j & 1]
        return {a for a, _ in active}, {b for _, b in active}
    count = 0
    for cut in range(1 << (n*n)):
        if not (n*n <= 3*cut.bit_count() <= 2*n*n):
            continue
        for left, right in product(cycles, repeat=2):
            hybrids = [(left & cut) | (right & ~cut), (right & cut) | (left & ~cut)]
            if any(h.bit_count() <= n and h not in cycles for h in hybrids):
                continue
            assert (left & cut).bit_count() == (right & cut).bit_count()
            assert endpoints(left & cut) == endpoints(right & cut)
            count += 1
    return count


if __name__ == "__main__":
    for m in (1, 2):
        actual = sum(all(i // m != dest // m for i, dest in enumerate(p))
                     for p in permutations(range(3*m)))
        assert actual == count_three_blocks(m)
    p = count_three_blocks(11)
    assert p == 17707661809258784033341440000000
    assert all(p * comb(33, k) > 2 * factorial(33) for k in (26, 27))
    for x, y in product(range(16), repeat=2):
        count = sum(z != 0 and z & ~x == 0 and z & ~y == 0 for z in range(16))
        assert count == (1 << (x & y).bit_count()) - 1
    print("Exact 33x33 counterexample and 256 four-bit separator examples verified")
    print(f"{check_hybrids(3)} sound hybrid pairs across all balanced 3x3 partitions")
