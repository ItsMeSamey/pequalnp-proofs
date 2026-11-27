"""Independent physical NAND and exterior oracles, including skip semantics."""
from itertools import product

from corridor_nand import compile_objective, corridor_witness, solve_compiled


def trace(raw, gates):
    physical = list(raw)
    for a, b in gates:
        physical.append(int(not (physical[a] and physical[b])))
    return physical


def accepts(w, clauses=(), pins=(), equalities=()):
    return (all(any(w[abs(l)-1] == int(l > 0) for l in row) for row in clauses)
            and all(w[v] == bit for v, bit in pins)
            and all(w[v] ^ w[u] == bit for v, u, bit in equalities))


def verify(n, gates, groups, exterior, budget, expected=None):
    source = compile_objective(n, gates, **exterior)
    primary_count, physical_gates, output = source
    assert primary_count == n and list(physical_gates[:len(gates)]) == list(gates)
    exists = False
    for raw in product(range(2), repeat=n):
        direct = accepts(trace(raw, gates), **exterior)
        assert bool(trace(raw, physical_gates)[output]) == direct
        exists |= direct
    wanted = expected or ("sat" if exists else "unsat")
    results = [corridor_witness(n, gates, groups, max_bad=budget, **exterior),
               solve_compiled(source, len(gates), groups, max_bad=budget, **exterior)]
    for status, word in results:
        assert status == wanted, (status, wanted, exterior)
        if status == "sat":
            assert len(word) == n and all(b in (0, 1) for b in word)
            assert accepts(trace(word, gates), **exterior)
            assert trace(word, physical_gates)[output] == 1
        else:
            assert word is None
    return source


def main():
    # Gate 0 materializes the private complement. Observe only three outputs.
    gates = [(1, 1), (0, 1), (3, 1), (4, 2)]
    groups = [[0, 1, 2, 3]]
    for bits in product(range(2), repeat=3):
        exterior = {"pins": list(zip((3, 4, 5), bits))}
        verify(2, gates, groups, exterior, 0, "skip")
        verify(2, gates, groups, exterior, 1)
    for ends in ((3, 4), (4, 5), (3, 5)):
        for bits in product(range(2), repeat=2):
            verify(2, gates, groups, {"pins": list(zip(ends, bits))}, 0)

    # Neither exterior names raw wire 0. Its two occurrences impose opposite
    # values when both taps are zero, so independent hidden lifts are unsound.
    shared = [(0, 1), (0, 0), (4, 2)]
    for bits in product(range(2), repeat=2):
        verify(3, shared, [[0], [1, 2]], {"pins": list(zip((3, 5), bits))}, 0)

    # Cross-block generated wire, ungrouped inverter, signed binary clause.
    network = [(0, 1), (2, 2), (2, 3)]
    verify(2, network, [[0], [2]], {"pins": [(4, 0)]}, 1)
    verify(2, network, [[0], [2]], {"clauses": [(-3, 4)], "pins": [(4, 1)]}, 1)

    # Interleaved A -> B -> A in the group graph remains a physical DAG.
    alternating = [(0, 0), (2, 1), (3, 0)]
    for bits in product(range(2), repeat=3):
        verify(2, alternating, [[2, 0], [1]], {"pins": list(zip((2, 3, 4), bits))}, 1)

    # Wide outward interface, one effective bit, no bad-block budget.
    copies = [(0, 1)] * 9
    for last in (0, 1):
        verify(2, copies, [list(range(9))],
               {"pins": [(i, 1) for i in range(2, 10)] + [(10, last)]}, 0)

    # Two exact-two port triples cannot be mutual complements. Budget counts
    # distinct bad tables before pinning or exterior propagation.
    twin = [(1, 1), (0, 1), (5, 1), (6, 4),
            (3, 3), (2, 3), (9, 3), (10, 8)]
    parts = [list(range(4)), list(range(4, 8))]
    for flip in (0, 1):
        constraints = {"equalities": [(5, 9, flip), (6, 10, flip), (7, 11, flip)]}
        verify(4, twin, parts, constraints, 1, "skip")
        verify(4, twin, parts, constraints, 2)

    pins = {"pins": [(3, 1)]}
    for malformed in ([[0, 1, 2, 3], [1]], [[0, 1, 2, 4]], [[0, 1]]):
        verify(2, gates, malformed, pins, 10, "skip")
    verify(3, [(0, 1), (3, 2)], [[0, 1]], {"pins": [(4, 1)]}, 10, "skip")

    # Change the asserted physical output while preserving a legal netlist.
    n, full, out = verify(2, gates, groups, {"pins": [(3, 0)]}, 0)
    changed = (n, full, (out+1) % (n+len(full)))
    assert solve_compiled(changed, len(gates), groups, pins=[(3, 0)]) == ("skip", None)
    print("physical corridor objective, bad-table caps, invisible sharing, malformed certificate")


if __name__ == "__main__":
    main()
