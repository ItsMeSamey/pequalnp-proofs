from itertools import product
from random import Random
from first_space import first_space
from graphic import is_graphic


def span(items):
    values = {0}
    for item in items:
        values |= {v ^ item for v in values}
    return values


def image(mask, vec):
    result = 0
    for i, v in enumerate(vec):
        if mask >> i & 1:
            result ^= v
    return result


def check(keys, tags, graphic=is_graphic):
    n = len(keys)
    active_sets = [sum(1 << i for i in range(n) if image(keys[i], chart) == tags[i])
                   for chart in product(range(4), repeat=2)]
    feasible = {s for s in range(1 << n) if not image(s, keys)
                and any(s & ~active == 0 for active in active_sets)}
    recovered = first_space(keys, tags, graphic=graphic)
    assert all(mask in feasible for mask in recovered)
    assert span(recovered) == span(feasible)
    return len(recovered)


if __name__ == "__main__":
    rng = Random(2658)
    ranks = []
    for _ in range(30):
        n = rng.randrange(2, 8)
        ranks.append(check([rng.randrange(4) for _ in range(n)],
                           [rng.randrange(4) for _ in range(n)]))
    print("30 first-space bases matched exhaustive charts; ranks", sorted(set(ranks)))
