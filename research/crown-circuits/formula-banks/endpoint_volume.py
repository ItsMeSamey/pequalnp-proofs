"""Check the seven endpoint-volume inequalities with exact rational arithmetic."""
from fractions import Fraction
from itertools import combinations


def profiles(budget, minimum=1):
    """Nondecreasing heavy weights with sum(weight minus one) at most budget."""
    yield ()
    for surplus in range(minimum, budget + 1):
        for tail in profiles(budget - surplus, surplus):
            yield (surplus + 1,) + tail


def lower_bound(weights, labels, maximal_counts):
    pairs = sorted(Fraction(1, 2 ** (a + b)) for a, b in combinations(weights, 2))
    slots = pairs[:maximal_counts[len(weights)]]
    for weight in weights:
        slots.extend([Fraction(1, 2 ** (weight + 1))] * 2)
    slots.extend([Fraction(1, 4)] * 4)
    if len(slots) >= labels:
        return sum(sorted(slots)[:labels])


def main():
    counts = [1]
    for h in range(1, 7):
        counts.append(max((d + 1) * counts[h - d - 1] for d in range(h)))
    assert counts == [1, 1, 2, 3, 4, 6, 9]
    for budget, labels, available in [(5, 12, 1), (6, 11, Fraction(1, 2))]:
        minima = {}
        for weights in profiles(budget):
            bound = lower_bound(weights, labels, counts)
            if bound is None:
                continue
            h = len(weights)
            if h not in minima or bound < minima[h][0]:
                minima[h] = (bound, weights)
        for h, (bound, weights) in sorted(minima.items()):
            assert bound > available
            print(f"surplus {budget}, labels {labels}, heavy count {h}, "
                  f"least bound {bound}, weights {weights}")


if __name__ == "__main__":
    main()
