"""Parallel bands, parameterized by the maximum cycle rank along the bridge corridor."""
from itertools import product
from random import Random
import networkx as nx
from strict_forest_reference import circles, swap


def solve(reference, triples, s, t):
    tours = circles(reference)
    disk = {x: v for v, tour in enumerate(tours) for x in tour}
    g = nx.MultiGraph()
    g.add_nodes_from(range(len(tours)))
    for i, (a, b, c) in enumerate(triples):
        if disk[b] != disk[c]:
            return False, None
        g.add_edge(disk[a], disk[b], key=i)
    bridges = [(u, v, next(iter(g[u][v]))) for u, v in nx.bridges(g)]
    core = g.copy()
    core.remove_edges_from(bridges)
    blocks = list(nx.connected_components(core))
    owner = {v: j for j, vs in enumerate(blocks) for v in vs}
    tree = nx.Graph()
    tree.add_nodes_from(range(len(blocks)))
    for u, v, i in bridges:
        tree.add_edge(owner[u], owner[v], gate=i)
    src, dst = owner[disk[s]], owner[disk[t]]
    if not nx.has_path(tree, src, dst):
        return True, None
    route = nx.shortest_path(tree, src, dst)
    mask = [0] * len(triples)
    for k, z in enumerate(route):
        ends = []
        variable = set()
        for adj, mark in [(k-1, s), (k+1, t)]:
            if not 0 <= adj < len(route):
                ends.append((mark, mark, None))
                continue
            gate = tree[z][route[adj]]["gate"]
            a, b, c = triples[gate]
            if disk[a] in blocks[z]:
                ends.append((a, a, None))
            else:
                ends.append((b, c, gate))
                variable.add(gate)
        terminals = {disk[x] for x, _, _ in ends}
        local = core.subgraph(blocks[z])
        ids = [i for _, _, i in local.edges(keys=True)]
        for u, v, i in local.edges(keys=True):
            if u in terminals or v in terminals or local.degree(u) != 2 or local.degree(v) != 2:
                variable.add(i)
        ordered = sorted(variable)
        for choice in product((0, 1), repeat=len(ordered)):
            for i, bit in zip(ordered, choice):
                mask[i] = bit
            cuts = [(triples[i][0], triples[i][1+mask[i]]) for i in ids]
            x, y = [b if i is not None and mask[i] else a for a, b, i in ends]
            if any(x in w and y in w for w in circles(swap(reference, cuts))):
                break
        else:
            return True, None
    cuts = [(a, (b, c)[bit]) for (a, b, c), bit in zip(triples, mask)]
    assert any(s in w and t in w for w in circles(swap(reference, cuts)))
    return True, mask


if __name__ == "__main__":
    rng = Random(979)
    yes = no = 0
    for n in range(1, 9):
        triples = [tuple(range(3*i, 3*i+3)) for i in range(n)]
        for _ in range(200):
            pools = [[] for i in range(rng.randint(1, n+1))]
            for a, b, c in triples:
                rng.choice(pools).append(a)
                rng.choice(pools).extend([b, c])
            ref = list(range(3*n))
            for pool in pools:
                rng.shuffle(pool)
                for i, x in enumerate(pool):
                    ref[x] = pool[(i+1) % len(pool)]
            s, t = rng.sample(range(3*n), 2)
            ok, mask = solve(ref, triples, s, t)
            assert ok
            expected = any(any(s in w and t in w for w in circles(swap(ref, [
                (a, (b, c)[v]) for (a, b, c), v in zip(triples, bits)])))
                           for bits in product((0, 1), repeat=n))
            assert expected == (mask is not None)
            yes += expected
            no += not expected
    print(f"1600 direct physical checks: {yes} YES and {no} NO.")
