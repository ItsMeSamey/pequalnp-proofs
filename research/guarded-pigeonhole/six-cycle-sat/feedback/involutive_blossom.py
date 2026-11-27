"""Polynomial matching solver for a closed ternary switch network."""
from collections import defaultdict

import networkx as nx

from check_involutive_turns import build, labels


def solve(sigma, r, s):
    """Return a mask joining wires r and s, or None. sigma lists off outputs."""
    n = len(sigma)
    if n % 3 or sorted(sigma) != list(range(n)):
        raise ValueError("expected one output permutation grouped in triples")
    if not (0 <= r < n and 0 <= s < n):
        raise ValueError("unknown marked wire")
    forbidden = [sigma[3*(i//3) + (i-1)%3] for i in range(n)]
    if any(forbidden[forbidden[i]] != i for i in range(n)):
        raise ValueError("forbidden turns must induce an involution")
    if r == s:
        return 0
    _, mate, incoming, outgoing, arcs = build(forbidden, n)
    graph = nx.Graph()
    ports = defaultdict(list)
    # Port i represents traversing its paired edge from i using directed arc i.
    for i, (u, _, j, _) in enumerate(arcs):
        ports[u].append(i)
        graph.add_edge(i, j)
    for u, group in ports.items():
        if u < mate[u]:
            for i in group:
                for j in ports.get(mate[u], ()):
                    if j != arcs[i][2]:
                        graph.add_edge(i, j)
    start, finish = len(arcs), len(arcs)+1
    graph.add_nodes_from((start, finish))
    graph.add_edges_from((start, i) for i in ports[outgoing[r]])
    graph.add_edges_from((finish, i) for i in ports[mate[incoming[s]]])
    matching = nx.max_weight_matching(graph, maxcardinality=True)
    if 2*len(matching) != len(graph):
        return None
    partner = dict(matching)
    partner.update((v, u) for u, v in matching)
    # Follow the augmenting component in the symmetric difference of matchings.
    i = partner[start]
    path = [r]
    turns = []
    while i != finish:
        _, _, j, tag = arcs[i]
        if tag is not None:
            u, setting = tag
            v = sigma[3*(u//3) + (u+setting)%3]
            if u != path[-1]:
                raise RuntimeError("discontinuous projected walk")
            if v in path:
                cut = path.index(v)
                del path[cut+1:]
                del turns[cut:]
            else:
                path.append(v)
                turns.append((u//3, setting))
        i = partner[j]
    bits = dict(turns)
    if path[-1] != s or any(bits[g] != h for g, h in turns):
        raise RuntimeError("invalid decoded path")
    return sum(h << g for g, h in bits.items())


if __name__ == "__main__":
    from random import Random
    from check_involutive_turns import involutions

    rng = Random(32971)
    models = queries = positives = 0
    for gates in (1, 2, 3):
        n = 3*gates
        candidates = list(involutions(list(range(n))))
        for forbidden in candidates if gates < 3 else rng.sample(candidates, 120):
            sigma = build(forbidden, n)[0]
            traces = [labels(sigma, m) for m in range(1 << gates)]
            models += 1
            for r in range(n):
                for s in range(n):
                    mask = solve(sigma, r, s)
                    truth = any(t[r] == t[s] for t in traces)
                    if truth != (mask is not None) or (truth and traces[mask][r] != traces[mask][s]):
                        raise RuntimeError((sigma, r, s, mask))
                    queries += 1
                    positives += truth
    print(models, "models,", queries, "queries,", positives, "witnesses,", queries-positives, "negatives")
