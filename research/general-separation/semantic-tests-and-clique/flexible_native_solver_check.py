"""Original-support checks of the flexible native solver."""
from itertools import combinations
from random import Random

from flexible_chain_control import graph_from_edges, parity_support, subsets
from flexible_native_solver import solve
from unittest.mock import patch


def verify(graph, pins, branch=None, cap=None):
    expected = any(parity_support(graph, extra | pins)
                   for extra in subsets(set(range(len(graph))) - pins))
    status, witness = solve(graph, pins, branch, cap)
    if status == "YES":
        assert expected and pins <= witness and parity_support(graph, witness)
    elif status == "NO":
        assert not expected and witness is None
    else:
        assert status == "UNKNOWN" and witness is None
    return status


def groups_case(m, cross_edges):
    edges = []
    n = 2*m
    for group in (range(m), range(m, 2*m)):
        for u, v in combinations(group, 2):
            edges.extend(((u, n), (v, n)))
            n += 1
    return graph_from_edges(n, edges + cross_edges)


if __name__ == "__main__":
    rng = Random(75231)
    counts = {"YES": 0, "NO": 0, "UNKNOWN": 0}
    base = list(combinations(range(5), 2))
    for mask in range(1 << len(base)):
        graph = graph_from_edges(5, [e for i, e in enumerate(base) if mask >> i & 1])
        for raw in combinations(range(5), 3):
            counts[verify(graph, set(raw))] += 1
    for _ in range(1000):
        n = rng.randrange(6, 11)
        graph = graph_from_edges(n, [e for e in combinations(range(n), 2)
                                     if rng.randrange(3) == 0])
        pins = set(rng.sample(range(n), rng.randrange(1,4)))
        branch = pins | {v for v in range(n) if rng.randrange(2)}
        counts[verify(graph, pins, branch, 5)] += 1
        assert verify(graph, pins, set(range(n))) != "UNKNOWN"
    m = 12
    for crossed, answer in [([(0,m)], "NO"),
                            ([(i, i+m) for i in range(m-1)], "YES")]:
        graph = groups_case(m, crossed)
        pins = {0, m, m-1}
        status, witness = solve(graph, pins, set(range(2*m)), 1)
        assert status == answer
        if witness is not None:
            assert pins <= witness and parity_support(graph, witness)
    # Many fixed pins make endpoint enumeration eligible despite a one-row NO.
    # Exercise the rank-first choice without depending on a time cutoff.
    a, b = 1, m+1
    internal = [(i, i+1) for i in (2,4,6,8, m+2,m+4,m+6,m+8)]
    graph = groups_case(m, [(a,b)] + internal)
    mandatory = {a,b,0,m,10,11,m+10,m+11}
    with patch("flexible_native_solver.subsets", side_effect=AssertionError("endpoint enumeration")):
        assert solve(graph, mandatory, set(range(2*m))) == ("NO", None)
    print(counts, "+ 1000 exact all-site and two large rank-one checks")
