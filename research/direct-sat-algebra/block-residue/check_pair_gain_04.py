"""Original NAND oracle and exhaustive matching-partition oracle for small DAGs."""
from functools import lru_cache
from itertools import combinations, product
from random import Random

from interval_optimizer import minimum_partition
from pair_optimizer import (best_partition, coarsened_interval_partition,
                            greedy_pair_partition, pair_interval_witness)


def cost_oracle(inputs, gates, observed):
    @lru_cache(None)
    def score(group):
        own = {inputs+i for i in group}
        incoming = set(v for i in group for v in gates[i]) - own
        if len(incoming) > 2:
            return None
        external_reads = {v for i, operands in enumerate(gates)
                          if i not in group for v in operands}
        visible = sorted((own | incoming) & (set(observed) | external_reads)
                         | {v for v in incoming if v >= inputs})
        entries = sorted(incoming)
        rows = set()
        for bits in product((0, 1), repeat=len(entries)):
            wire = dict(zip(entries, bits))
            for i in sorted(group):
                a, b = gates[i]
                wire[inputs+i] = int(not (wire[a] and wire[b]))
            rows.add(tuple(wire[v] for v in visible))
        # Intersect all binary and unary projections by enumerating assignments.
        scopes = list(combinations(range(len(visible)), 2))
        scopes.extend((i,) for i in range(len(visible)))
        tables = [{tuple(row[i] for i in ix) for row in rows} for ix in scopes]
        for row in product((0, 1), repeat=len(visible)):
            if row not in rows and all(tuple(row[i] for i in ix) in table
                                       for ix, table in zip(scopes, tables)):
                return 1
        return 0
    return score


def pair_optimum(score, rest):
    if not rest:
        return 0
    x, *tail = rest
    choices = [score((x,)) + pair_optimum(score, tail)]
    for i, y in enumerate(tail):
        weight = score((x, y))
        if weight is not None:
            choices.append(weight + pair_optimum(score, tail[:i]+tail[i+1:]))
    return min(choices)


def interval_optimum(score, n):
    values = [0]
    for end in range(1, n+1):
        values.append(min(values[start]+val for start in range(end)
                          if (val := score(tuple(range(start, end)))) is not None))
    return values[-1]


def check(inputs, gates, pins):
    observed = {v for v, _ in pins}
    score = cost_oracle(inputs, gates, observed)
    ids = tuple(range(len(gates)))
    baseline = sum(score((x,)) for x in ids)
    optimum = pair_optimum(score, ids)
    greedy, pairs = greedy_pair_partition(inputs, gates, observed)
    best, groups = best_partition(inputs, gates, observed)
    coarse, merged = coarsened_interval_partition(inputs, gates, observed)
    for total, family in ((greedy, pairs), (coarse, merged), (best, groups)):
        assert sorted(i for group in family for i in group) == list(ids)
        assert sum(score(tuple(g)) for g in family) == total
    assert all(len(group) in (1, 2) for group in pairs)
    assert 0 <= baseline-optimum <= 2*(baseline-greedy)
    seed_cost, bounds = minimum_partition(inputs, gates, observed)
    assert seed_cost == interval_optimum(score, len(gates))
    seed = [set(range(a, b)) for a, b in bounds]
    def merged_score(blocks):
        return score(tuple(sorted(set.union(*(seed[k] for k in blocks)))))
    coarsest = pair_optimum(merged_score, tuple(range(len(seed))))
    for block in merged:
        pieces = [s for s in seed if s & set(block)]
        assert len(pieces) <= 2 and set.union(*pieces) == set(block)
    assert 0 <= seed_cost-coarsest <= 2*(seed_cost-coarse)
    assert (best, groups) == ((coarse, merged) if coarse <= greedy else (greedy, pairs))
    def accepts(raw):
        wire = list(raw)
        for a, b in gates:
            wire.append(int(not (wire[a] and wire[b])))
        return all(wire[v] == bit for v, bit in pins)
    solved, chosen, raw = pair_interval_witness(inputs, gates, pins=pins)
    assert solved == best and chosen == groups
    assert (raw is not None) == any(accepts(r) for r in product(range(2), repeat=inputs))
    if raw is not None:
        assert len(raw) == inputs and accepts(raw)
    return baseline, optimum


def main():
    gates = [(0, 1), (0, 2)]
    for b, q in product(range(2), repeat=2):
        assert check(2, gates, [(1, b), (3, q)]) == (2, 0)
    interleaved = [(0, 1), (2, 3), (0, 4), (2, 5)]
    check(4, interleaved, [(1, 1), (3, 1), (6, 1), (7, 1)])
    rng = Random(19827)
    for _ in range(75):
        inputs = rng.randrange(1, 5)
        gates = [(rng.randrange(inputs+i), rng.randrange(inputs+i))
                 for i in range(rng.randrange(1, 7))]
        pins = [(v, rng.randrange(2)) for v in range(inputs+len(gates))
                if rng.randrange(3) == 0]
        check(inputs, gates, pins)
    print("80 original NAND instances, exhaustive pair partitions, gain-two and half-saving bound")


if __name__ == "__main__":
    main()
