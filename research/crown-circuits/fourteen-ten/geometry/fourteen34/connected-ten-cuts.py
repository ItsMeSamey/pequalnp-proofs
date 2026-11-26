"""Find archived forbidden edge patterns among the thirteen connected boundary cases."""
from pathlib import Path
import networkx as nx
from networkx.algorithms.isomorphism import GraphMatcher
root = Path(__file__).resolve().parents[2]
patterns = []
for row in (root / "degree/t13-seven/graph-cut/initial-drat.tsv").read_text().splitlines():
    n, mask, budget = map(int, row.split()[:3])
    pattern = nx.Graph()
    pattern.add_nodes_from(range(n))
    pattern.add_edges_from((i,j) for j in range(n) for i in range(j)
                           if mask >> (j*(j-1)//2+i)&1)
    if nx.is_connected(pattern) and budget+1>=n-1:
        patterns.append((n,mask,budget,pattern))
for line in (root / "degree/t14-34/eight-connected-ten.tsv").read_text().splitlines()[1:]:
    label=line.split()[0]
    host=nx.from_graph6_bytes(label.encode())
    for n,mask,budget,pattern in patterns:
        mapping=next(GraphMatcher(host,pattern).subgraph_monomorphisms_iter(),None)
        if mapping is not None:
            injection={i:v for v,i in mapping.items()}
            print(label,n,mask,budget,*(injection[i] for i in range(n)),flush=True)
            break
    else:
        print(label,'survives',flush=True)
