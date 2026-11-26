"""Exhaustive projected truth tables for the native permutation arms."""
from itertools import permutations, product


def subsets(mask):
    x = mask
    while x:
        yield x
        x = (x - 1) & mask
    yield 0


def arm(order, marked):
    """Enumerate actual chain bits, all permitted source bits, and sinks."""
    r = len(order)
    accepted = set()
    for terminal, chain in product(range(1 << r), repeat=2):
        if any((chain >> k) & 1 and
               (((terminal >> j) ^ (chain >> (k + 1))) & 1) != 1
               for k, j in enumerate(order)):
            continue
        allowed = sum(1 << j for k, j in enumerate(order)
                      if (chain >> (k + 1)) & 1)
        for source in subsets(allowed):
            if not marked or source:
                public = source | (terminal << r) if marked else terminal | (source << r)
                accepted.add(public)
    return accepted


def hull(points):
    if not points:
        return set()
    origin = next(iter(points))
    basis = {}
    for x in points:
        v = origin ^ x
        while v:
            i = v.bit_length() - 1
            if i not in basis:
                basis[i] = v
                break
            v ^= basis[i]
    flat = {origin}
    for v in basis.values():
        flat |= {x ^ v for x in flat}
    return flat


def main():
    pairs = 0
    for r in range(2, 5):
        orders = list(permutations(range(r)))
        alice = {o: arm(o, True) for o in orders}
        bob = {o: arm(o, False) for o in orders}
        for a, b in product(orders, repeat=2):
            assert bool(alice[a] & bob[b]) == (a != b)
            pairs += 1
    rounds = 0
    for r in range(3, 8):
        order = tuple(range(r))
        a, b = arm(order, True), arm(order, False)
        live = set(range(1 << (2*r)))
        for s in range(r, 2, -1):
            live = hull(a & live) & hull(b & live)
            mask = (1 << (s-1)) - 1
            assert live == {x | (y << r) for x in subsets(mask) for y in subsets(mask)}
            rounds += 1
        while live:
            updated = hull(a & live) & hull(b & live)
            assert len(updated) < len(live)
            live = updated
    count = 0
    for word in range(1 << 9):
        rows = [(word >> (3*i)) & 7 for i in range(3)]
        points = {u | (v << 3) for u, v in product(range(8), repeat=2)
                  if all(not (u >> i) & 1 or (row & v).bit_count() % 2
                         for i, row in enumerate(rows))}
        for i, j in product(range(3), repeat=2):
            answer = any((x >> i) & 1 and not ((x >> 3) & ~(1 << j)) for x in points)
            assert answer == bool((rows[i] >> j) & 1)
        if all(rows):
            assert len(hull(points)) == 64
        count += 1
    print(f'{pairs} permutation pairs, {rounds} exact slow affine rounds, '
          f'{count} matrix summaries with every query passed.')


if __name__ == '__main__':
    main()
