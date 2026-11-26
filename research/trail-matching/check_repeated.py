"""Check individual branches of the repeated-start-pattern perfect-matching solver."""
from collections import defaultdict
from itertools import product
from check import Graph, completes, pair_trails


def compile_branch(masks, offset, paths, groups, guess):
    graph = Graph()
    transitions = [graph.vertices(4) for _ in masks]
    for i, (before, pivot, after, d) in enumerate(transitions):
        graph.edge(before, after)
        graph.edge(d, pivot)
        graph.edge(d, after if offset >> i & 1 else before)
    singleton_sources = [[] for path in paths]
    start_rhs = [0] * len(paths)
    wires = [None] * len(masks)
    repeated_index = 0

    def parity_gate(arity, rhs):
        ports = graph.vertices(arity)
        graph.clique(ports + graph.vertices((arity ^ rhs) & 1))
        return ports

    for pattern, group in groups.items():
        if len(pattern) == 1:
            singleton_sources[pattern[0]].extend(group)
        if len(pattern) > 1:
            rhs = guess >> repeated_index & 1
            repeated_index += 1
            for j in pattern:
                start_rhs[j] ^= rhs
            for i, v in zip(group, parity_gate(len(group), rhs)):
                wires[i] = v
    free = []
    for j, path in enumerate(paths):
        first, *other = parity_gate(1 + len(singleton_sources[j]), start_rhs[j])
        graph.edge(first, transitions[path[0]][0])
        for i, v in zip(singleton_sources[j], other):
            wires[i] = v
        for i, k in zip(path, path[1:]):
            graph.edge(transitions[i][2], transitions[k][0])
        free.append(transitions[path[-1]][2])
    missing = [i for i, v in enumerate(wires) if v is None]
    reservoir = graph.vertices(len(missing) + len(free))
    for i,v in zip(missing,reservoir):
        wires[i] = v
    for f,v in zip(free,reservoir[len(missing):]):
        graph.edge(f,v)
    graph.clique(reservoir + graph.vertices(len(graph.adjacency) & 1))
    marked = [(row[1],v) for row,v in zip(transitions,wires)]
    for u,v in marked:
        graph.edge(u,v)
    return graph.adjacency, marked


def audit(masks, offsets):
    count = 0
    for paths in pair_trails(masks):
        groups = defaultdict(list)
        for i in range(len(masks)):
            groups[tuple(j for j, path in enumerate(paths) if masks[path[0]] >> i & 1)].append(i)
        repeated = [sum(1 << i for i in group) for pat, group in groups.items() if len(pat)>1]
        if not repeated:
            continue
        for b in offsets:
            for guess in range(1 << len(repeated)):
                graph = compile_branch(masks, b, paths, groups, guess)
                for x in range(1 << len(masks)):
                    valid = all(not (x >> i & 1) or (m & x).bit_count() % 2 == (b >> i & 1)
                                for i,m in enumerate(masks))
                    inferred = sum(((m & x).bit_count() % 2) << j for j,m in enumerate(repeated))
                    assert completes(*graph,x) == (valid and guess == inferred)
                    count += 1
    return count


if __name__ == '__main__':
    for n in (2,3):
        print(n,sum(audit(m, range(1 << n)) for m in product(range(1 << n), repeat=n)), flush=True)
