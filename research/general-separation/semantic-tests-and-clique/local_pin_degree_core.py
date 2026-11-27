"""Bounded regression for the local-complement/deletion proof-degree descent."""
from bounded_cubic_pin_pc import pc, flat_truth
from one_missing_reservoir_check import FIXTURE
from three_pin_degree_profile import GRAPH, PINS


def complement(rows, v):
    neighbors = rows[v]
    return [row ^ ((neighbors ^ (1 << i)) if neighbors & (1 << i) else 0)
            for i, row in enumerate(rows)]


def delete(rows, pins, v):
    lower = (1 << v) - 1
    return ([(row & lower) | ((row >> (v + 1)) << v)
             for i, row in enumerate(rows) if i != v],
            tuple(p - int(p > v) for p in pins))


def pair_counts(rows, pins, degree):
    status = []
    for v in range(len(rows)):
        if v in pins:
            continue
        children = [delete(host, pins, v) for host in (rows, complement(rows, v))]
        certified = tuple(pc(A, P, degree)[0] for A, P in children)
        assert flat_truth(rows, pins) == any(flat_truth(A, P) for A, P in children)
        status.append(certified)
    return status


def core(rows, pins, degree):
    assert not pc(rows, pins, degree)[0]
    while len(rows) > len(pins):
        reduced = None
        for v in range(len(rows)):
            if v in pins:
                continue
            for host in (rows, complement(rows, v)):
                child = delete(host, pins, v)
                if not pc(*child, degree)[0]:
                    reduced = child
                    break
            if reduced:
                break
        if reduced is None:
            assert not flat_truth(rows, pins)
            return rows, pins
        rows, pins = reduced
    assert flat_truth(rows, pins)
    return None


def main():
    for graph, pins in [(FIXTURE, (0,1,2)), (GRAPH, PINS)]:
        for degree in (2,3):
            status = pair_counts(graph, pins, degree)
            pair_proofs = sum(all(pair) for pair in status)
            print(len(graph), degree, len(status), pair_proofs)
    result = core(GRAPH, PINS, 2)
    assert result is not None
    graph, pins = result
    print("unrefuted degree-two core", len(graph), graph, pins)
    assert pc(graph, pins, 3)[0]
    assert all(all(pair) for pair in pair_counts(graph, pins, 2))
    # Exhaust all input assignments under each local complement on both fixtures.
    for graph, pins in [(FIXTURE, (0,1,2)), (GRAPH, PINS)]:
        for v in set(range(len(graph))).difference(pins):
            other = complement(graph,v)
            for x in range(1 << len(graph)):
                if not all(x & (1 << i) for i in pins):
                    continue
                y = (graph[v] & x).bit_count() & 1
                new = x ^ ((1 ^ y) << v)
                def violations(A, word):
                    return sum((1 << j) for j, row in enumerate(A)
                               if word & (1 << j) and (word & row).bit_count() % 2)
                assert violations(other,new) == violations(graph,x)


if __name__ == "__main__":
    main()
