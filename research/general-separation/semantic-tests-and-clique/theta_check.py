"""Exact dynamic programming for vertex-branching trees on joins of C5."""
from functools import lru_cache

FULL = 31
NEIGHBORS = [(1 << ((j - 1) % 5)) | (1 << ((j + 1) % 5)) for j in range(5)]
EDGES = [((1 << j) | (1 << ((j + 1) % 5))) for j in range(5)]

@lru_cache(None)
def canonical(mask):
    images = []
    for direction in (-1, 1):
        for offset in range(5):
            images.append(sum(1 << ((offset + direction * j) % 5)
                              for j in range(5) if mask & (1 << j)))
    return min(images)

def omega(mask):
    if any((e & mask) == e for e in EDGES):
        return 2
    return int(bool(mask))

def optimal_leaves(m, half, upper):
    # threshold k or k-1/2, and additive bias of 0 or 1/64
    threshold64 = 64 * (2 * m + 1) - 32 * half
    @lru_cache(None)
    def solve(included, masks):
        untouched = masks.count(FULL)
        integral = included + sum(omega(mask) for mask in masks if mask != FULL)
        remaining = threshold64 - 64 * integral - upper
        if remaining > 0 and 5 * (64 * untouched) ** 2 < remaining ** 2:
            return 1
        best = None
        for mask in set(masks):
            others = list(masks)
            others.remove(mask)
            for j in range(5):
                if not mask & (1 << j):
                    continue
                present = tuple(sorted(others + [canonical(mask & NEIGHBORS[j])]))
                absent = tuple(sorted(others + [canonical(mask & ~(1 << j))]))
                cost = solve(included + 1, present) + solve(included, absent)
                best = cost if best is None else min(best, cost)
        assert best is not None
        return best
    return solve(0, (FULL,) * m)

if __name__ == "__main__":
    for half in (0, 1):
        for upper in (0, 1):
            obtained = [optimal_leaves(m, half, upper) for m in range(1, 8)]
            expected = [2 ** max(0, m - (2 if half else 4)) for m in range(1, 8)]
            assert obtained == expected
            print("half-threshold offset", half, "upper bias /64", upper, "leaves", obtained)
