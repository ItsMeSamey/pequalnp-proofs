"""Eleven-vertex connected, subcubic, 14-edge hosts with one branching separator."""
from collections import defaultdict, Counter
from itertools import permutations, combinations, combinations_with_replacement, product
from pathlib import Path
import networkx as nx
root=Path(__file__).resolve().parents[2]
bad={h:bytearray(1<<(h*(h-1)//2)) for h in (5,6)}
def bit(i,j):
    a,b=sorted((i,j))
    return 1<<(b*(b-1)//2+a)
for line in (root/'degree/t13-seven/graph-cut/initial-drat.tsv').read_text().splitlines():
    h,m,lim=map(int,line.split()[:3])
    if h not in bad or lim+1<h-1:continue
    es=[(i,j) for j in range(h) for i in range(j) if m&bit(i,j)]
    g=nx.Graph();g.add_nodes_from(range(h));g.add_edges_from(es)
    if not nx.is_connected(g):continue
    for p in permutations(range(h)):
        bad[h][sum(bit(p[i],p[j]) for i,j in es)]=1
for h,flags in bad.items():
    for mask,exclude in enumerate(flags):
        if exclude:
            for j in range(h*(h-1)//2):
                flags[mask|1<<j]=1
def ok(g):
    for h,flags in bad.items():
        for block in combinations(g.nodes,h):
            mask=sum(1<<(j*(j-1)//2+i) for j in range(h) for i in range(j)
                     if g.has_edge(block[i],block[j]))
            if flags[mask]:return False
    return True
def add(bag,g):
    h=(len(g),g.number_of_edges(),tuple(sorted(d for v,d in g.degree())))
    if any(nx.is_isomorphic(g,f) for f in bag[h]):return
    bag[h].append(g.copy())
def allowed(g):
    return 2<=len(g)<=8 and nx.is_connected(g) and max(dict(g.degree()).values())<=3 and ok(g)
pool=defaultdict(list)
for g in nx.graph_atlas_g():
    if allowed(g):add(pool,g)
# An eight-vertex component can occur only alongside K2. It has 10 or 11 edges.
# Every such connected subcubic graph has a vertex of degree <3, so appending
# a fresh path of length 12−e supplies a connected graph in the 12-edge ledger.
eights=defaultdict(list)
for line in (root/'verification/threshold-twelve/connected-graphs.txt').read_text().splitlines():
    n,*rows=map(int,line.split())
    if n not in (9,10):continue
    g=nx.Graph();g.add_nodes_from(range(n));g.add_edges_from((i,j) for i in range(n) for j in range(i) if rows[i]>>j&1)
    for v,d in g.degree():
        if d!=1:continue
        path={v}
        if n==10:
            a=next(iter(g[v]))
            if g.degree(a)!=2:continue
            path.add(a)
        f=g.subgraph(set(g)-path).copy()
        if ok(f):add(eights,f)
for gs in eights.values():
    for g in gs:add(pool,g)
by=defaultdict(list)
for gs in pool.values():
    for g in gs:by[len(g),g.number_of_edges()].append(g)
counts=Counter(); survivors=defaultdict(list)
for d in (2,3):
    for l in range(d-1):
        for c in range(2,d-l+1):
            for keys in combinations_with_replacement(sorted(by),c):
                if sum(v for v,e in keys)!=10-l or sum(e for v,e in keys)!=14-d:continue
                for blocks in product(*(by[k] for k in keys)):
                    body=nx.disjoint_union_all(blocks)
                    for links in combinations([v for v,z in body.degree() if z<3],d-l):
                        g=body.copy()
                        g.add_edges_from((10,v) for v in links)
                        g.add_edges_from((10,len(body)+j) for j in range(l))
                        if not nx.is_connected(g):continue
                        counts['attachments']+=1
                        if ok(g):
                            counts['allowed attachments']+=1;add(survivors,g)
print('admissible 8-vertex component counts',[(k[:2],len(gs)) for k,gs in eights.items()])
print(dict(counts))
for gs in survivors.values():
    for g in gs:
        g=nx.convert_node_labels_to_integers(g,ordering='sorted')
        print(nx.to_graph6_bytes(g,header=False).decode().strip(),sorted(d for v,d in g.degree()))
print('distinct surviving unmarked hosts',sum(map(len,survivors.values())))
