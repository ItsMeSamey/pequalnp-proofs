"""Exact rooted routing using the cycle rank of a supplied reference's union graph."""
from itertools import product
import networkx as nx
from strict_forest_reference import circles,swap


def corridors(graph, terminals):
    incident = {v: list(graph.edges(v, keys=True)) for v in graph}
    used = set()
    chains = []
    for vertex in terminals:
        for _, other, index in incident[vertex]:
            if index in used:
                continue
            path = [index]
            used.add(index)
            while other not in terminals:
                _, other, index = next(e for e in incident[other] if e[2] not in used)
                path.append(index)
                used.add(index)
            chains.append(path)
    assert len(used) == graph.number_of_edges()
    return chains


def satisfy(n, pins, clauses):
    """Subset reachability over nonunit clauses; integer bitset witness per state."""
    states = {0: 0}
    gains = [[0,0] for _ in range(n)]
    for j, clause in enumerate(clauses):
        if not clause:
            return None
        for i, bit in clause:
            gains[i][bit] |= 1 << j
    for i, (left,right) in enumerate(gains):
        new = {}
        for state,mask in states.items():
            for bit in ((pins[i],) if i in pins else (0,1)):
                new[state | (right if bit else left)] = mask | (bit << i)
        states = new
    return states.get((1 << len(clauses))-1)


def solve(reference, triples, s, t):
    """Gate (a,b,c) swaps successor a with b on 0, c on 1."""
    owner = {x:j for j,cycle in enumerate(circles(reference)) for x in cycle}
    graph = nx.MultiGraph()
    graph.add_nodes_from(owner.values())
    options = []
    for i,(a,b,c) in enumerate(triples):
        ends = [(b,None)] if owner[b]==owner[c] else [(b,0),(c,1)]
        for x,value in ends:
            graph.add_edge(owner[a],owner[x],key=len(options))
            options.append((i,value))
    roots = {owner[s],owner[t]}
    component = nx.node_connected_component(graph,owner[s])
    if owner[t] not in component:
        return None
    graph = graph.subgraph(component).copy()
    leaves = [v for v in graph if v not in roots and graph.degree(v)<=1]
    while leaves:
        v = leaves.pop()
        if v in graph and v not in roots and graph.degree(v)<=1:
            leaves.extend(graph[v])
            graph.remove_node(v)
    terminals = roots | {v for v in graph if graph.degree(v)!=2}
    choices = sorted({options[k][0] for v in terminals for _,_,k in graph.edges(v,keys=True)})
    chains = corridors(graph,terminals)
    for assignment in product((0,1),repeat=len(choices)):
        for states in product((False,True),repeat=len(chains)):
            pins = dict(zip(choices,assignment))
            clauses = []
            consistent = True
            for chain,active in zip(chains,states):
                literals = [options[k] for k in chain if options[k][1] is not None]
                if not active:
                    clauses.append([(i,1-x) for i,x in literals])
                else:
                    for i,x in literals:
                        if pins.setdefault(i,x)!=x:
                            consistent = False
                            break
                if not consistent:
                    break
            if not consistent:
                continue
            mask = satisfy(len(triples),pins,clauses)
            if mask is None:
                continue
            bits = [(mask>>i)&1 for i in range(len(triples))]
            perm = swap(reference,[(a,(b,c)[x]) for (a,b,c),x in zip(triples,bits)])
            if any(s in row and t in row for row in circles(perm)):
                return bits
    return None
