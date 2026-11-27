"""Exact-first matching branch with optional one-sided search on the residual label."""
import networkx as nx

from bipartite_matching_hull import solve as hull_solve
from planar_ternary_matching import count as planar_count
from potential_labelled_matching import search as owner_search
from ternary_labelled_matching import search as random_search


def search(n, edges, target, *, owner_kappa, planar_cap, rounds, randbelow_fn, metrics):
    graph = nx.Graph()
    graph.add_nodes_from(range(n))
    graph.add_edges_from((u, v) for u, v, _ in edges)

    def residual(n, edges, target, *, rounds, randbelow_fn):
        status, ids, _ = owner_search(n, edges, target, kappa_cap=owner_kappa)
        metrics["owner_calls"] += 1
        if status != "UNKNOWN":
            return status, ids
        if planar_cap is not None and len(target) <= planar_cap and nx.check_planarity(graph)[0]:
            hits, ids = planar_count(n, edges, target)
            metrics["planar_calls"] += 1
            return ("SAT" if hits else "UNSAT"), ids
        if rounds:
            metrics["random_calls"] += 1
            return random_search(n, edges, target, rounds=rounds, randbelow_fn=randbelow_fn)
        return "UNKNOWN", None

    if nx.is_bipartite(graph):
        metrics["hull_calls"] += 1
        status, ids, _ = hull_solve(n, edges, target, backend=residual,
                                    rounds=rounds, randbelow_fn=randbelow_fn)
        return status, ids
    return residual(n, edges, target, rounds=rounds, randbelow_fn=randbelow_fn)
