"""Check the incidence-surplus cases for arbitrary independent OR banks."""
from fractions import Fraction
from endpoint_volume import lower_bound, profiles


def main():
    pair_counts = [h * (h - 1) // 2 for h in range(7)]
    for initial, labels, available in [(5, 12, 1), (6, 11, Fraction(1, 2))]:
        for extra in range(1, initial + 1):
            bounds = []
            for weights in profiles(initial - extra):
                volume = lower_bound(weights, labels - extra, pair_counts)
                if volume is not None:
                    bounds.append(volume)
            if not bounds:
                print(f"Surplus {initial}, excess memberships {extra}, too few pair slots")
                continue
            least = min(bounds)
            assert least >= available  # at least one large label adds positive measure
            print(f"Surplus {initial}, excess memberships {extra}, pair volume {least}")


if __name__ == "__main__":
    main()
