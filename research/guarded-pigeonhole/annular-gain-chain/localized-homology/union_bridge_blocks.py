"""Exact rooted routing using bridge blocks of the supplied reference's union graph."""
from itertools import product
from random import Random

import networkx as nx

from strict_forest_reference import circles, swap
from union_band_core import corridors, satisfy


def locally_join(reference, triples, options, graph, endpoints, fixed):
    """Return just this block's owned assignments or None."""
    terminals = {v for v in graph if graph.degree(v) != 2}
    terminals.update(e[0] for e in endpoints)
    edges = [key for _, _, key in graph.edges(keys=True)]
    owned = {options[key][0] for key in edges}
    portal_gates = {gate for _, _, _, gate in endpoints if gate is not None}
    owned.update(portal_gates)
    choices = portal_gates | {options[k][0] for v in terminals for _, _, k in graph.edges(v, keys=True)}
    choices = sorted(choices - fixed.keys())
    chains = corridors(graph, terminals)
    optional = [[options[k] for k in chain if options[k][1] is not None] for chain in chains]
    for values in product((0, 1), repeat=len(choices)):
        base = dict(fixed)
        base.update(zip(choices, values))
        for through in product(*[(True,) if not lits else (False, True) for lits in optional]):
            pins = base.copy()
            clauses = []
            for active, literals in zip(through, optional):
                if active:
                    if any(pins.setdefault(i, bit) != bit for i, bit in literals):
                        break
                else:
                    clauses.append([(i, 1-bit) for i, bit in literals])
            else:
                word = satisfy(len(triples), pins, clauses)
                if word is None:
                    continue
                values_here = {i: (word >> i) & 1 for i in owned}
                cuts = []
                for k in edges:
                    i, literal = options[k]
                    bit = values_here[i]
                    if literal is None or literal == bit:
                        a, b, c = triples[i]
                        cuts.append((a, (b, c)[bit]))
                x, y = [c if g is not None and values_here[g] else b for _, b, c, g in endpoints]
                if any(x in tour and y in tour for tour in circles(swap(reference, cuts))):
                    return values_here
    return None


def solve(reference, triples, s, t):
    """Return physical 0/1 choices, or None when the marks cannot join."""
    disk = {x: j for j, cycle in enumerate(circles(reference)) for x in cycle}
    g = nx.MultiGraph()
    g.add_nodes_from(disk.values())
    options = []
    for i, (a, b, c) in enumerate(triples):
        ends = [(b, None)] if disk[b] == disk[c] else [(b, 0), (c, 1)]
        for x, bit in ends:
            g.add_edge(disk[a], disk[x], key=len(options))
            options.append((i, bit))
    bridges = [(u, v, next(iter(g[u][v]))) for u, v in nx.bridges(g)]
    core = g.copy()
    core.remove_edges_from(bridges)
    blocks = list(nx.connected_components(core))
    owner = {v: i for i, block in enumerate(blocks) for v in block}
    tree = nx.Graph()
    tree.add_nodes_from(range(len(blocks)))
    for u, v, key in bridges:
        tree.add_edge(owner[u], owner[v], key_id=key)
    src, dst = owner[disk[s]], owner[disk[t]]
    if not nx.has_path(tree, src, dst):
        return None
    path = nx.shortest_path(tree, src, dst)
    endpoints = [[] for _ in path]
    endpoints[0].append((disk[s], s, s, None))
    endpoints[-1].append((disk[t], t, t, None))
    fixed = {}
    for j, (left, right) in enumerate(zip(path, path[1:])):
        i, lit = options[tree[left][right]["key_id"]]
        a, b, c = triples[i]
        if lit is None:
            variable_end = (disk[b], b, c, i)
        else:
            if fixed.setdefault(i, lit) != lit:
                return None
            x = (b, c)[lit]
            variable_end = (disk[x], x, x, None)
        for endpoint in [(disk[a], a, a, None), variable_end]:
            dest = j if owner[endpoint[0]] == left else j+1
            endpoints[dest].append(endpoint)
    assignment = fixed.copy()
    for z, portals in zip(path, endpoints):
        local = locally_join(reference, triples, options, core.subgraph(blocks[z]), portals, fixed)
        if local is None:
            return None
        for i, bit in local.items():
            assert assignment.setdefault(i, bit) == bit
    bits = [assignment.get(i, 0) for i in range(len(triples))]
    cuts = [(a, (b, c)[bit]) for (a, b, c), bit in zip(triples, bits)]
    assert any(s in w and t in w for w in circles(swap(reference, cuts)))
    return bits


if __name__ == "__main__":
    rng = Random(149)
    yes = no = 0
    for n in range(1, 7):
        triples = [tuple(range(3*i, 3*i+3)) for i in range(n)]
        for _ in range(250):
            pools = [[] for i in range(rng.randint(1, 2*n+1))]
            for a, b, c in triples:
                rng.choice(pools).append(a)
                exclusive = rng.choice(pools)
                exclusive.append(b)
                (rng.choice(pools) if rng.randrange(2) else exclusive).append(c)
            ref = list(range(3*n))
            for pool in pools:
                rng.shuffle(pool)
                for j, x in enumerate(pool):
                    ref[x] = pool[(j+1) % len(pool)]
            s, t = rng.sample(range(3*n), 2)
            bits = solve(ref, triples, s, t)
            expected = any(any(s in w and t in w for w in circles(swap(ref, [
                (a, (b, c)[bit]) for (a, b, c), bit in zip(triples, choices)])))
                           for choices in product((0, 1), repeat=n))
            assert expected == (bits is not None)
            yes += expected
            no += not expected
    print(f"1500 direct physical checks: {yes} YES and {no} NO.")
