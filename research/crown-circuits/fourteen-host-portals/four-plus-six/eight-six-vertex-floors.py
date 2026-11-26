"""Embed checked finite OR obstructions into each surviving six-flag graph."""
from itertools import permutations
from pathlib import Path
import networkx as nx


def bit(i, j):
    return 1 << (max(i, j)*(max(i, j)-1)//2+min(i,j))


def embeddings(n, mask):
    edges=[(i,j) for j in range(n) for i in range(j) if mask&bit(i,j)]
    return [(sum(bit(p[i],p[j]) for i,j in edges),p) for p in permutations(range(6),n)]


source=Path(__file__).resolve().parents[2]/'thirteen-exact/degree/t13-seven/graph-cut/initial-drat.tsv'
known=[list(map(int, line.split()[:3])) for line in source.read_text().splitlines()]
bank=[(n,m,r,embeddings(n,m)) for n,m,r in known if n<=6]
for g in nx.graph_atlas_g():
    if len(g)!=6 or not nx.is_connected(g) or max(dict(g.degree()).values())>3 or g.number_of_edges() not in (8,9):
        continue
    mask=sum(bit(i,j) for i,j in g.edges())
    matches=[(r,n,m,p) for n,m,r,images in bank for subset,p in images if subset&mask==subset]
    print(g.name, g.number_of_edges(),mask,max(matches,default=None))
