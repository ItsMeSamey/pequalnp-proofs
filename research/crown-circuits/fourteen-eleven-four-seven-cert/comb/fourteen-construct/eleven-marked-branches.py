from collections import Counter
from pathlib import Path
import networkx as nx

def name(g):
    if len(g) == 2:
        return 'K2'
    if max(dict(g.degree()).values()) <= 2:
        return ('C' if g.number_of_edges() == len(g) else 'P') + str(len(g))
    if len(g) == 4 and g.number_of_edges() == 4:
        return 'paw'
    return 'connected-cubic'

rows = ['large_graph\tbranch\tdegree\tremaining_components\tstatus']
for graph_id in (446,447,448,450):
    graph = nx.graph_atlas(graph_id)
    for flag, degree in graph.degree():
        rest = graph.copy()
        rest.remove_node(flag)
        shapes = sorted(name(rest.subgraph(c)) for c in nx.connected_components(rest))
        result = 'excluded' if shapes == ['connected-cubic'] else 'additional floor needed'
        rows.append(f'{graph_id}\t{flag}\t{degree}\t{"+".join(shapes)}\t{result}')
Path('eleven-marked-branches.tsv').write_text('\n'.join(rows)+'\n')
print(Counter(row.split('\t')[-1] for row in rows[1:]))
