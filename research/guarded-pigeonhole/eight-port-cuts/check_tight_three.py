"""A tight cut of size three joining two alternating five-vertex paths."""
from itertools import combinations
import networkx as nx
from check import dec, proper

g=nx.Graph()
for offset in (0,5):
    nx.add_path(g,range(offset,offset+5))
cut=[(0,5),(2,7),(4,9)]
g.add_edges_from(cut)
ports=[0,1,3,4,5,6,8,9]
left=[0,4,6,8]
right=[1,3,5,9]
assert all(2*len(nx.max_weight_matching(g.subgraph(set(g)-{a,b}),maxcardinality=True))==8
           for a,b in g.edges())
counts={}
for a in combinations(left,2):
    for b in combinations(right,2):
        blue=set(a+b)
        colors=[int(v not in blue) for v in ports]
        mono1=(1 in blue)==(3 in blue)
        mono2=(6 in blue)==(8 in blue)
        verdict=dec(g,ports,colors,set(range(5)))
        sat=proper(g,ports,colors)
        assert verdict=='UNKNOWN' or (verdict=='SAT')==sat
        if mono1 and mono2:assert verdict!='UNKNOWN'
        key=(mono1 and mono2,verdict)
        counts[key]=counts.get(key,0)+1
print('tight P5 pair:',counts)
