"""Exact one-round pair coarsening of physical NAND block seeds (NetworkX 3.7)."""
from itertools import combinations

from corridor_nand import _net, _rows, corridor_witness
from pair_optimizer import _Costs, _intervals, _singletons


def _optimize(costs, seed):
    import networkx as nx
    if nx.__version__ != "3.7":
        raise RuntimeError(f"expected NetworkX 3.7, found {nx.__version__}")
    seed = tuple(tuple(sorted(group)) for group in seed)
    covered = sorted(i for group in seed for i in group)
    if any(not group for group in seed) or covered != list(range(len(costs.gates))):
        raise ValueError("seed must partition all original gate indices")
    original = [costs.score(group) for group in seed]
    if None in original:
        raise ValueError("seed block has more than two distinct physical inputs")
    graph = nx.Graph()
    graph.add_nodes_from(range(len(seed)))
    for i, j in combinations(range(len(seed)), 2):
        merged = tuple(sorted(seed[i] + seed[j]))
        score = costs.score(merged)
        if score is not None:
            gain = original[i] + original[j] - score
            if gain > 0:
                graph.add_edge(i, j, weight=gain)
    matching = nx.max_weight_matching(graph, maxcardinality=False, weight="weight",
                                      backend="networkx")
    groups = []
    occupied = set()
    score = sum(original)
    for i, j in matching:
        if i == j or i in occupied or j in occupied or not graph.has_edge(i, j):
            raise AssertionError("matching backend returned invalid edge set")
        occupied.update((i, j))
        groups.append(tuple(sorted(seed[i] + seed[j])))
        score -= graph[i][j]["weight"]
    groups.extend(group for i, group in enumerate(seed) if i not in occupied)
    result = tuple(sorted(groups))
    costs.verify(result, score)
    return score, result


def exact_pair_partition(inputs, gates, observed=(), *, seed=None):
    """Optimize disjoint pair merges from the supplied seed or all singletons."""
    costs = _Costs(inputs, gates, observed)
    return _optimize(costs, _singletons(costs) if seed is None else seed)


def best_exact_partition(inputs, gates, observed=()):
    """Compare exact single-round coarsenings; prefer interval seed on ties."""
    costs = _Costs(inputs, gates, observed)
    singles = _optimize(costs, _singletons(costs))
    intervals = _optimize(costs, _intervals(costs))
    return intervals if intervals[0] <= singles[0] else singles


def exact_pair_witness(inputs, gates, *, clauses=(), pins=(), equalities=()):
    """Return (bad, groups, status, raw); backend failures propagate as exceptions."""
    gates = _net(inputs, gates)
    clauses, pins, equalities = (tuple(map(tuple, data))
                                for data in (clauses, pins, equalities))
    rows = _rows(inputs + len(gates), clauses, pins, equalities)
    observed = {abs(l)-1 for row in rows for l in row}
    bad, groups = best_exact_partition(inputs, gates, observed)
    status, raw = corridor_witness(inputs, gates, groups, clauses=clauses, pins=pins,
                                  equalities=equalities, max_bad=bad)
    if status not in ("sat", "unsat"):
        raise AssertionError("verified physical partition was skipped")
    return bad, groups, status, raw
