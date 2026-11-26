"""Test all candidate branching flags in the q12 disconnected ledger."""
import csv
from pathlib import Path
from collections import Counter
import networkx as nx
atlas=nx.graph_atlas_g()
def graph(s):
    return atlas[int(s[1:])] if s.startswith('G') and s[1:].isdigit() else nx.from_graph6_bytes(s.encode())
def qualifies(h):
    n=len(h); m=h.number_of_edges(); d=max(dict(h.degree()).values(),default=0)
    return m>=2 and d<m and (d>=3 or n==5 and m==5)
counts=Counter(); missing=[]
with Path(__file__).with_suffix('.tsv').open('w') as f:
    print('orders','graphs','possible_marks',sep='\t',file=f)
    for row in csv.DictReader(Path(__file__).with_name('twelve-disconnected.tsv').open(),delimiter='\t'):
        parts=[graph(x) for x in row['components'].split(',')]
        marks=[]
        for i,g in enumerate(parts):
            for w,d in g.degree():
                if d<2:continue
                if d>3:marks.append(f'{i}:{w}');continue
                h=g.copy();h.remove_node(w);h.remove_nodes_from(list(nx.isolates(h)))
                others=[k for j,k in enumerate(parts) if j!=i]+[h.subgraph(c) for c in nx.connected_components(h)]
                if not any(qualifies(k) for k in others):marks.append(f'{i}:{w}')
        counts[(row['orders'],bool(marks))]+=1
        if marks:missing.append((row['components'],marks))
        print(row['orders'],row['components'],','.join(marks) or '-',sep='\t',file=f)
print(sorted(counts.items()))
print('remaining',len(missing),missing)
