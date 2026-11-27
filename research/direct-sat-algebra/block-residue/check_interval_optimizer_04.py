"""Independent tiny truth-table/partition oracle for the fixed-order optimizer."""
from itertools import combinations, product
from random import Random

from interval_optimizer import interval_witness, minimum_partition


def trace(raw, gates):
    values = list(raw)
    for x, y in gates:
        values.append(int(not (values[x] and values[y])))
    return values


def interval_cost(inputs, gates, ids, observations):
    local_gates = set(ids)
    produced = {inputs + i for i in ids}
    reads = {x for i in ids for x in gates[i]}
    outside = sorted(reads - produced)
    if len(outside) > 2:
        return None
    external_reads = {x for i, gate in enumerate(gates) if i not in local_gates for x in gate}
    visible = sorted((produced | set(outside)) & (observations | external_reads)
                     | {x for x in outside if x >= inputs})
    images = set()
    for bits in product((0, 1), repeat=len(outside)):
        word = dict(zip(outside, bits))
        for i in ids:
            x, y = gates[i]
            word[inputs+i] = int(not (word[x] and word[y]))
        images.add(tuple(word[x] for x in visible))
    for triple in combinations(images, 3):
        majority = tuple(int(sum(bits) >= 2) for bits in zip(*triple))
        if majority not in images:
            return 1
    return 0


def partitions(size):
    if size == 0:
        yield ()
        return
    for mask in range(1 << (size - 1)):
        cuts = [0] + [i for i in range(1, size) if mask >> (i-1) & 1] + [size]
        yield tuple(zip(cuts, cuts[1:]))


def oracle(inputs, gates, pins, equalities, clauses):
    observed = {x for x, _ in pins}
    observed.update(x for a, b, _ in equalities for x in (a, b))
    observed.update(abs(lit)-1 for row in clauses for lit in row)
    costs = {}
    for i in range(len(gates)):
        for j in range(i+1, len(gates)+1):
            costs[i, j] = interval_cost(inputs, gates, range(i, j), observed)
    scores = {}
    for parts in partitions(len(gates)):
        values = [costs[key] for key in parts]
        if None not in values:
            scores[parts] = sum(values)
    best = min(scores.values())
    optimum, parts = minimum_partition(inputs, gates, observed)
    assert scores.get(parts) == optimum == best, (inputs, gates, observed, optimum, best)

    solutions = set()
    for raw in product((0, 1), repeat=inputs):
        values = trace(raw, gates)
        if (all(values[x] == d for x, d in pins)
                and all((values[x] ^ values[y]) == d for x, y, d in equalities)
                and all(any(values[abs(lit)-1] == int(lit > 0) for lit in row)
                        for row in clauses)):
            solutions.add(raw)
    b, partition, witness = interval_witness(inputs, gates, clauses=clauses,
                                              pins=pins, equalities=equalities)
    assert b == best and scores.get(partition) == best
    assert (witness is None) == (not solutions)
    if witness is not None:
        assert tuple(witness) in solutions
    return best, bool(solutions)


def main():
    oracle(0, [], [], [], [])
    oracle(2, [], [(1, 1)], [(0, 1, 1)], [])
    oracle(0, [], [], [], [()])
    # All three physical NAND coordinates are observed. No single majority
    # closed table fits. Its output can take either requested value.
    for target in (0, 1):
        assert oracle(2, [(0, 1)], [(2, target)], [], [(1, -1), (2, -2)]) == (1, True)
    for target in (0, 1):
        assert oracle(1, [(0, 0)], [(0, 1), (1, target)], [], []) == (0, target == 0)
    # Two individually bad factors have four distinct entrances, so their
    # union is inadmissible. The complete projected relation is observed.
    assert oracle(4, [(0, 1), (2, 3)], [(4, 1), (5, 1)], [],
                  [(i, -i) for i in range(1, 5)]) == (2, True)
    # Raw a appears across both sides of a possible cut; an internal gate
    # can be the designated output even though later gates still consume it.
    gates = [(0, 1), (2, 3), (0, 4), (3, 3), (6, 5)]
    for wire in range(8):
        for value in (0, 1):
            oracle(3, gates, [(wire, value)], [(0, 5, 1)], [(3, -7)])
    rng = Random(184301)
    for _ in range(64):
        n = rng.randint(1, 4)
        gates = [(rng.randrange(n+i), rng.randrange(n+i)) for i in range(rng.randrange(7))]
        wires = n + len(gates)
        output = rng.randrange(wires)
        clauses = [tuple(rng.choice((-1, 1))*rng.randint(1, wires) for _ in range(k))
                   for k in [rng.choice((1, 2)), rng.choice((1, 2))]]
        eq = [(rng.randrange(wires), rng.randrange(wires), rng.randrange(2))]
        for target in (0, 1):
            oracle(n, gates, [(output, target)], eq, clauses)
    print("interval costs, partition optimum and original raw witnesses verified")


if __name__ == "__main__":
    main()
