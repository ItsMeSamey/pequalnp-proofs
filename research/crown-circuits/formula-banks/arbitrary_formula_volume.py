"""Exact slot-volume checks for arbitrary monotone endpoint-tail formulas."""
from fractions import Fraction
from itertools import combinations
from endpoint_volume import lower_bound, profiles


def refined_minima(weights, clean_limit):
    edges = list(combinations(range(len(weights)), 2))
    pair_cost = [Fraction(1, 2 ** (weights[i] + weights[j])) for i, j in edges]
    minima = []
    cases = 0
    for size in range(clean_limit + 1):
        least = None
        for clean in combinations(range(len(edges)), size):
            cases += 1
            touched = {v for j in clean for v in edges[j]}
            slots = [2 * cost for j, cost in enumerate(pair_cost) if j not in clean]
            for i, weight in enumerate(weights):
                ordinary = Fraction(1, 2 ** (weight + 1))
                slots.extend([ordinary, 2 * ordinary if i in touched else ordinary])
            slots.extend([Fraction(1, 4)] * 4)
            rest = 12 - size
            if len(slots) < rest:
                continue
            volume = sum(pair_cost[j] for j in clean) + sum(sorted(slots)[:rest])
            if least is None or volume < least:
                least = volume
        minima.append(least)
    return cases, minima


def main():
    pair_counts = [h * (h - 1) // 2 for h in range(7)]
    for budget, count, available in [(5, 12, 1), (6, 11, Fraction(1, 2))]:
        remaining = []
        for weights in profiles(budget):
            bound = lower_bound(weights, count, pair_counts)
            if bound is not None and bound <= available:
                remaining.append(weights)
        print(f"Surplus {budget}, coarse exceptions {remaining}")
        if budget == 6:
            assert not remaining
        else:
            assert set(remaining) == {(2, 2, 2, 2, 2), (2, 2, 2, 3)}
        for weights in remaining:
            cases, minima = refined_minima(weights, 6 if len(weights) == 5 else 4)
            assert min(minima) == Fraction(9, 8)
            print(f"{weights}, {cases} subsets, minima " + ", ".join(map(str, minima)))


if __name__ == "__main__":
    main()
