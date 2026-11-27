"""Exhaustive external-pin checks for joint-reset-gate-tail.md."""
from fractions import Fraction
from itertools import product


def inspect(pins, moves):
    # Each reset clears the named bit when its full pattern matches.
    controls = [dict(zip("xyz", bits)) for bits in product(range(2), repeat=3)]
    rows = [row for row in controls if all(row[k] == v for k, v in pins.items())]
    resets = [(bit, pattern) for bit, pattern in moves
              if any(all(row[k] == v for k, v in pattern.items()) for row in rows)]
    canonical = [row for row in rows if not any(
        all(row[k] == v for k, v in pattern.items()) for _, pattern in resets)]
    # Constant-true residual. For the tail use two independent weights on x,y.
    activities = [('x', 1), ('y', 2)]
    scopes = [set(pattern) - pins.keys() for _, pattern in resets]
    scopes.extend([{bit} - pins.keys() for bit, _ in activities])
    read = max([1] + [sum(bit in scope for scope in scopes) for bit in 'xyz'])
    # Compute the exact read-th power of V for t=2, k=2.
    bound = Fraction(len(rows), 4) ** read
    for _, pattern in resets:
        good = sum(not all(row[k] == v for k, v in pattern.items()) for row in rows)
        bound *= Fraction(good, len(rows))
    for bit, weight in activities:
        bound *= Fraction(sum(2 ** (read * weight * row[bit]) for row in rows), len(rows))
    tail = sum(row['x'] + 2 * row['y'] >= 2 for row in canonical)
    assert tail ** read <= bound
    return len(rows), len(canonical), tail, read, bound


if __name__ == '__main__':
    clear_x = ('x', {'x': 1})
    clear_z = ('z', {'z': 1})
    assert inspect({'x': 1}, [clear_x]) == (4, 0, 0, 1, 0)
    assert inspect({'x': 1}, []) == (4, 4, 2, 1, 5)
    assert inspect({'x': 1}, [clear_z]) == (4, 2, 1, 1, Fraction(5, 2))
    assert inspect({'y': 1}, [clear_x, clear_z]) == (4, 1, 1, 2, 10)
    assert inspect({}, [clear_x, clear_z]) == (8, 2, 1, 2, Fraction(85, 4))
    print("Five exhaustive pin, reset, and weighted-tail cases passed.")
