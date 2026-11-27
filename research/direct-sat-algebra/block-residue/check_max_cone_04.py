"""Exact all-subsets oracle for one arbitrary union of a supplied gate partition."""
from itertools import combinations, product
from random import Random

from check_pair_gain_04 import cost_oracle
from max_cone import cone_witness, maximum_cone_partition


def check(n, gates, seed, pins=(), equalities=(), clauses=()):
    seen = {v for v, _ in pins}
    seen.update(v for x, y, _ in equalities for v in (x, y))
    seen.update(abs(l)-1 for row in clauses for l in row)
    score = cost_oracle(n, gates, seen)
    blocks = [tuple(sorted(s)) for s in seed]
    costs = [score(s) for s in blocks]
    best = sum(costs)
    for size in range(2, len(seed)+1):
        for chosen in combinations(range(len(seed)), size):
            joined = tuple(sorted(i for b in chosen for i in blocks[b]))
            cost = score(joined)
            if cost is not None:
                best = min(best, sum(costs)-sum(costs[b] for b in chosen)+cost)
    actual, groups = maximum_cone_partition(n, gates, seen, seed=seed)
    assert sorted(i for g in groups for i in g) == list(range(len(gates)))
    assert actual == best == sum(score(tuple(sorted(g))) for g in groups)
    changed = 0
    for group in groups:
        parts = [set(s) for s in blocks if set(s).intersection(group)]
        assert set().union(*parts) == set(group)
        changed += len(parts) > 1
    assert changed <= 1
    def accepted(raw):
        wire = list(raw)
        for a, b in gates:
            wire.append(int(not (wire[a] and wire[b])))
        return (all(wire[v] == bit for v, bit in pins)
                and all(wire[x] ^ wire[y] == d for x, y, d in equalities)
                and all(any(wire[abs(l)-1] == (l > 0) for l in row) for row in clauses))
    verdict = any(accepted(raw) for raw in product(range(2), repeat=n))
    solved, chosen, raw = cone_witness(n, gates, seed=seed, pins=pins,
                                       equalities=equalities, clauses=clauses)
    assert solved == best and (raw is not None) == verdict
    if raw is not None:
        assert len(raw) == n and all(v in (0, 1) for v in raw) and accepted(raw)
    return sum(costs), best


def main():
    # Producing group A also consumes the output of B. Raw entrance x and
    # the product of the enclosed gate are legal starting boundary pairs.
    cyclic = [(0, 0), (2, 1), (3, 0)]
    for bits in product(range(2), repeat=3):
        check(2, cyclic, [(2, 0), (1,)], list(zip((2, 3, 4), bits)))

    # Duplicates yield three simultaneously bad singleton relations when all
    # are separate. Their only inputs a,b become private after the full union.
    triples = [(0, 1)]*3
    for bits in product(range(2), repeat=3):
        assert check(2, triples, [(2,), (0,), (1,)], list(zip((2, 3, 4), bits))) == (3, 0)

    # p is a produced, live boundary coordinate. The full gate set has three
    # primary entrances; the exact optimum merges only the three consumers.
    generated = [(0, 1), (3, 2), (3, 2), (3, 2)]
    for bits in product(range(2), repeat=3):
        assert check(3, generated, [(i,) for i in range(4)],
                     list(zip((4, 5, 6), bits))) == (3, 0)

    rng = Random(172316)
    for _ in range(80):
        n = rng.randrange(1, 5)
        gates = [(rng.randrange(n+i), rng.randrange(n+i))
                 for i in range(rng.randrange(1, 8))]
        wires = n+len(gates)
        pins = [(v, rng.randrange(2)) for v in range(wires) if rng.randrange(4) == 0]
        eqs = [(rng.randrange(wires), rng.randrange(wires), rng.randrange(2))]
        clauses = [(rng.randrange(1, wires+1), -rng.randrange(1, wires+1))]
        score = cost_oracle(n, gates, ())
        seed = [(i,) for i in range(len(gates))]
        for _ in range(len(gates)):
            if len(seed) < 2:
                break
            i, j = sorted(rng.sample(range(len(seed)), 2))
            union = tuple(sorted(seed[i]+seed[j]))
            if score(union) is not None:
                seed[i] = union
                seed.pop(j)
        rng.shuffle(seed)
        check(n, gates, seed, pins, eqs, clauses)
    print("104 physical circuits, all seed subsets, noncontiguous cyclic seed and internal boundary")


if __name__ == "__main__":
    main()
