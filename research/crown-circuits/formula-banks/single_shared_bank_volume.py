"""Exact pair-slot bounds in a preprocessing network with one shared OR aggregate."""
from fractions import Fraction
from functools import cache
from itertools import combinations
from endpoint_volume import profiles

MAXIMAL_SETS = (1, 1, 2, 3, 4, 6, 9)


@cache
def pair_minimum(weights, count, forbidden=()):
    edges = [edge for edge in combinations(range(len(weights)), 2) if edge not in forbidden]
    costs = [Fraction(1, 2 ** (weights[i] + weights[j])) for i, j in edges]
    least = None
    for size in range(min(len(edges), count, MAXIMAL_SETS[len(weights)]) + 1):
        for clean in combinations(range(len(edges)), size):
            touched = {v for i in clean for v in edges[i]}
            slots = [2 * c for i, c in enumerate(costs) if i not in clean]
            for v, weight in enumerate(weights):
                ordinary = Fraction(1, 2 ** (weight + 1))
                slots.extend([ordinary, (1 + (v in touched)) * ordinary])
            slots += [Fraction(1, 4)] * 4
            required = count - size
            if len(slots) < required:
                continue
            bound = sum(costs[i] for i in clean) + sum(sorted(slots)[:required])
            if least is None or bound < least[0]:
                least = (bound, {size})
            elif bound == least[0]:
                least[1].add(size)
    return least


def first_pass(labels, budget, capacity):
    exceptions = []
    for reuse in range(2, budget + 2):
        for group in range(2, max(2, budget - reuse + 2) + 1):
            for inside in range(budget - reuse + 2):
                for outside in range(budget - reuse + 2 - inside):
                    surplus = budget - (reuse - 1) - inside - outside
                    for weights in profiles(surplus):
                        singles = max(0, group - inside)
                        available_weights = sorted((*weights, *([1] * singles)), reverse=True)
                        local = sum(Fraction(1, 2 ** d) for d in available_weights[:singles])
                        if local > 1 or (group > singles and local == 1):
                            continue
                        pairs = pair_minimum(weights, labels - group - outside)
                        if pairs is not None and pairs[0] < capacity:
                            exceptions.append((reuse, group, inside, outside, weights))
    return exceptions


def final_pass(labels, group, weights):
    h = len(weights)
    least = None
    equal_cases = set()
    for nc in range(min(2, h) + 1):
        for common in combinations(range(h), nc):
            rest = [v for v in range(h) if v not in common]
            for np in range(min(group, len(rest)) + 1):
                for private in combinations(rest, np):
                    local = sum(Fraction(1, 2 ** weights[j]) for j in private)
                    local += Fraction(group - np, 2)
                    if local > 1:
                        continue
                    common_weight = sum(weights[j] for j in common) + 2 - nc
                    forbidden = tuple((i, j) for i, j in combinations(range(h), 2)
                                      if (i in common and j in common + private) or
                                         (j in common and i in common + private))
                    pairs = pair_minimum(weights, labels - group, forbidden)
                    if pairs is None:
                        continue
                    bound = pairs[0] + local / 2 ** common_weight
                    if least is None or bound < least:
                        least, equal_cases = bound, set()
                    if bound == least:
                        equal_cases.update((common, private, size) for size in pairs[1])
    return least, equal_cases


def main():
    for labels, budget, capacity in [(12, 5, 1), (11, 6, Fraction(1, 2))]:
        exceptions = first_pass(labels, budget, capacity)
        print(f"{labels} labels: {len(exceptions)} first-pass exceptions")
        for reuse, group, inside, outside, weights in exceptions:
            assert (reuse, inside, outside) == (2, 0, 0)
            bound, equality = final_pass(labels, group, weights)
            assert bound is not None and bound >= capacity
            print(f"  group={group}, weights={weights}, bound={bound}")
            if bound == capacity:
                assert (labels, group, weights) == (12, 4, (2, 2, 2, 2))
                assert equality == {((), (0, 1, 2, 3), 4)}
                print("  Equality forces four private heavy banks and four clean heavy pairs.")


if __name__ == "__main__":
    main()
