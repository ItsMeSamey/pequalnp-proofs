"""Reconcile the five analytic exclusions with the surviving marked-host ledger."""
from collections import Counter
from pathlib import Path
import sys
import networkx as nx

counts = Counter()
hosts = set()
for line in Path(sys.argv[1]).read_text().splitlines():
    fields = line.split()
    if len(fields) != 2 or fields[1] == '-':
        continue
    code, marks = fields
    graph = nx.from_graph6_bytes(code.encode())
    hosts.add(code)
    for w in map(int, marks.split(',')):
        residual = graph.copy()
        residual.remove_nodes_from([w] + [i for i in graph[w] if graph.degree(i) == 1])
        parts = sorted((residual.subgraph(c) for c in nx.connected_components(residual)), key=len)
        sizes = tuple(map(len, parts))
        assert sum(sizes) == 11 and max(dict(graph.degree()).values()) <= 3
        if sizes == (3,3,5):
            assert max(dict(parts[-1].degree()).values()) == 3 and parts[-1].number_of_edges() == 5
        if sizes == (3,4,4):
            assert tuple(h.number_of_edges() for h in parts) == (3,4,4)
        counts[sizes] += 1
assert counts == {(3,8):52,(4,7):157,(5,6):40,(3,3,5):8,(3,4,4):6}
assert len(hosts) == 206
print(len(hosts),sum(counts.values()),sorted(counts.items()))
