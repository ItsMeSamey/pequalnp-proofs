"""Exact limiting arithmetic for 16 and 100 epochs under the residual recensus."""
from fractions import Fraction

for excess, epochs, expected in [
    (Fraction(59, 1000), 16, Fraction(1593, 1600)),
    (Fraction(149, 2500), 100, Fraction(9983, 10000)),
]:
    available = Fraction(2)
    remaining = excess
    epoch = excess / epochs
    for _ in range(epochs):
        assert available > 24 * remaining
        t = 1 + (7 * available + 16 * remaining) // (available - 24 * remaining)
        assert t >= 8
        assert available * (t-7) > (24*t+16) * remaining
        available -= t * epoch
        remaining -= epoch
        assert available * (t-7) > (24*t+16) * remaining
    assert 2 - available == expected < 1
    print(excess, epochs, expected)
