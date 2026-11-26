"""Whole-graph enumeration using the companion check.py's independent boundary solver."""
from collections import Counter, defaultdict
from itertools import product
from random import Random
import networkx as nx
from check import odd_solutions


def build(rows, n):
    graph = nx.Graph()
    edges, pairs, ports, blocks = [], [], [], []
    tests, field, truth = defaultdict(list), {}, {}

    def vertices(k):
        block = list(range(len(graph), len(graph)+k))
        graph.add_nodes_from(block)
        return block

    def add(u, v):
        assert u != v and not graph.has_edge(u, v)
        graph.add_edge(u, v)
        edges.append((u, v))
        return len(edges)-1

    for j,row in enumerate(rows):
        for c in range(3):
            for i,(v,neg) in enumerate(row[:c+1]):
                tests[v].append(((j,c,i), neg if i == c else 1-neg))
    for v in range(n):
        block = vertices(2*max(2,len(tests[v])))
        ids = [add(block[i-1],block[i]) for i in range(len(block))]
        truth[v] = ids[0]
        for i,(key,failed_at) in enumerate(tests[v]):
            field[key] = ids[2*i+1-failed_at]
        ports.append(block[0])
        blocks.append(block)
    for j,row in enumerate(rows):
        block = vertices(10)
        pos = 2
        for c,length in enumerate((3,3,5)):
            path = [block[0], *block[pos:pos+length-1], block[1]]
            ids = [add(u,v) for u,v in zip(path,path[1:])]
            for i in range(c+1):
                pairs.append((field[j,c,i],ids[2*i]))
            pos += length-1
        ports.append(block[2])
        blocks.append(block)
    if not blocks:
        a,b = vertices(2)
        add(a,b)
        return graph,edges,pairs,truth,[a,b]
    path = vertices(2*len(blocks))
    for u,v in zip(path,path[1:]):
        add(u,v)
    for j,port in enumerate(ports):
        add(port,path[2*j])
        blocks[j].extend(path[2*j:2*j+2])
    return graph, edges, pairs, truth, sum(blocks,[])


def verify(rows,n):
    graph,edges,pairs,truth,order = build(rows,n)
    assert nx.is_connected(graph) and nx.is_bipartite(graph)
    assert nx.check_planarity(graph)[0] and max(dict(graph.degree()).values()) <= 3
    assert nx.approximation.treewidth_min_degree(graph)[0] <= 2
    assert len(pairs) == 6*len(rows) and len(set(i for pair in pairs for i in pair)) == 2*len(pairs)
    positions = {v:i for i,v in enumerate(order)}
    if max(Counter(v for row in rows for v,_ in row).values(),default=0)<=4:
        assert max(abs(positions[u]-positions[v]) for u,v in edges)<=51
    degrees = [0]*len(graph)
    for i,(u,v) in enumerate(edges):
        degrees[u] |= 1<<i
        degrees[v] |= 1<<i
    conflicts = [(1<<a) | (1<<b) for a,b in pairs]
    totals = Counter()
    number = 0
    for mask in odd_solutions(graph,edges):
        number += 1
        if any(mask & p == p for p in conflicts):
            continue
        assert all((mask & d).bit_count() == 1 for d in degrees)
        totals[tuple((mask>>truth[v]) & 1 for v in range(n))] += 1
    for x in product(range(2),repeat=n):
        assert totals[x] == int(all(any(x[v]^neg for v,neg in row) for row in rows))
    return number,sum(totals.values())


if __name__ == '__main__':
    cases = [(3,[tuple((i,s[3*j+i]) for i in range(3)) for j in range(2)])
             for s in product(range(2),repeat=6)]
    cases += [(0,[]),(1,[]),(4,[]),(4,[((0,1),)*3]),
              (1,[((0,0),)*3, ((0,1),)*3]),(2,[((0,0),(0,1),(1,0)), ((1,1),)*3])]
    rng = Random(971)
    for _ in range(50):
        n = rng.randrange(1,4)
        cases.append((n,[[(rng.randrange(n),rng.randrange(2)) for _ in range(3)]
                         for _ in range(rng.randrange(1,5))]))
    result = [verify(rows,n) for n,rows in cases]
    print(len(cases),'graphs;',sum(a for a,b in result),'all-odd subgraphs;',
          sum(b for a,b in result),'admissible matchings;',sum(b==0 for a,b in result),'UNSAT')
