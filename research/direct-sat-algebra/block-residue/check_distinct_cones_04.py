"""Compare maximal cones with every admissible set partition and every raw word."""
from itertools import product
from random import Random
from check_pair_gain_04 import cost_oracle
from distinct_cones import distinct_cone_witness, maximal_cone_partition


def partitions(n):
    if not n:
        yield ()
        return
    i = n-1
    for prior in partitions(i):
        yield prior + ((i,),)
        for j in range(len(prior)):
            yield prior[:j] + (prior[j]+(i,),) + prior[j+1:]


def check(n, gates, output=None, clauses=(), equalities=(), pins=()):
    observed = {abs(l)-1 for row in clauses for l in row}
    observed.update(v for v, bit in pins)
    observed.update(v for x, y, bit in equalities for v in (x, y))
    if output is not None:
        observed.add(output)
    score = cost_oracle(n, gates, observed)
    reported, groups = maximal_cone_partition(n, gates, observed)
    maximal = [set(g) for g in groups]
    assert sorted(i for g in groups for i in g) == list(range(len(gates)))
    assert sum(score(tuple(sorted(g))) for g in groups) == reported
    best = len(gates)+1
    for partition in partitions(len(gates)):
        costs = [score(block) for block in partition]
        if None in costs:
            continue
        assert all(sum(set(block) <= cone for cone in maximal) == 1 for block in partition)
        best = min(best, sum(costs))
    assert reported == best
    def accepts(raw):
        wire = list(raw)
        for a, b in gates:
            wire.append(int(not (wire[a] and wire[b])))
        return ((output is None or wire[output]) and
                all(wire[v] == bit for v, bit in pins) and
                all(wire[x] ^ wire[y] == bit for x, y, bit in equalities) and
                all(any(wire[abs(l)-1] == int(l > 0) for l in row) for row in clauses))
    exists = any(accepts(word) for word in product(range(2), repeat=n))
    state, cost, solved_groups, raw = distinct_cone_witness(
        n, gates, clauses=clauses, pins=pins, equalities=equalities, output=output)
    assert state == ("sat" if exists else "unsat")
    assert cost == best
    assert {frozenset(g) for g in solved_groups} == {frozenset(g) for g in groups}
    if exists:
        assert len(raw) == n and all(bit in (0, 1) for bit in raw) and accepts(raw)
    else:
        assert raw is None
    return maximal


def main():
    check(2, [], output=0, clauses=[(-1,)])
    check(2, [], output=0)
    # A,B,A,B with A producing an entry for B. The nested cone starting from
    # (wire 0, gate 0's output) uses ancestor-related seeds.
    interleaved = [(0, 1), (3, 2), (0, 3), (2, 4)]
    for signed in (-7, 7):
        groups = check(3, interleaved, output=5, clauses=[(signed,)])
        assert {frozenset(g) for g in groups} == {frozenset((0, 2)), frozenset((1, 3))}
    # Equal definitions produce physically distinct legal operands.
    repeated = [(0, 1), (1, 0), (2, 3), (3, 2)]
    for flip in (0, 1):
        check(2, repeated, output=4, equalities=[(4, 5, flip)])
    rng = Random(976415)
    for case in range(100):
        n = rng.randrange(2, 6)
        gates = [tuple(rng.sample(range(n+i), 2)) for i in range(case % 7)]
        wires = n + len(gates)
        pins = [(v, rng.randrange(2)) for v in range(wires) if rng.randrange(7) == 0]
        clauses = [tuple(rng.choice((-1, 1)) * rng.randrange(1, wires+1)
                         for _ in range(rng.randrange(1, 3)))]
        eqs = [(rng.randrange(wires), rng.randrange(wires), rng.randrange(2))]
        check(n, gates, rng.randrange(wires), clauses, eqs, pins)
    # Crossing cones and cyclic quotients when tied inputs are allowed.
    for n, gates in [(3, [(0, 0), (0, 1), (0, 2)]), (2, [(0, 0), (2, 1), (3, 0)])]:
        assert maximal_cone_partition(n, gates) is None
        assert distinct_cone_witness(n, gates, clauses=[()]) == ("skip", None, None, None)
    print("106 tied-free instances, every gate partition and raw assignment; two tied abstentions")


if __name__ == "__main__":
    main()
