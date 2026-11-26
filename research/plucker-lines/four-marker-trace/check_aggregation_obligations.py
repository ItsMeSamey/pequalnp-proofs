"""Finite independent check of simultaneous obligation discharge."""
from itertools import product

def nonempty_sets(n):
    return tuple(frozenset(i for i in range(n) if m >> i & 1)
                 for m in range(1, 1 << n))

def check():
    # Two-bit restriction allows exhaustive checking of all local cell pairs.
    # Collapse each mode to possible triples (outstanding hit, raw hit, real hit).
    statuses = set()
    tables = nonempty_sets(4)
    for left, right, target in product(tables, tables, range(4)):
        real = any(target ^ b in left for b in right)
        for partner in right:
            raw = (target ^ partner) in left
            for assigned in (False, True):
                statuses.add((assigned and raw, raw, real))
    aggregates = 0
    for states in product(statuses, repeat=3):
        obligation, raw, real = map(any, zip(*states))
        assert (not obligation or raw) and (not raw or real)
        aggregates += 1
    print(f"Verified {aggregates} three-mode truth profiles")
if __name__ == "__main__":
    check()
