from collections import defaultdict
from math import comb,factorial,perm
import networkx as nx
from graph7 import graphs
groups=defaultdict(list)
for g in graphs():
 assert g.number_of_edges()==7 and min(dict(g.degree()).values())>0
 groups[g.number_of_nodes()].append(g)
for v,gs in sorted(groups.items()):
 bins=defaultdict(list);mass=0
 for g in gs:
    bins[tuple(sorted(dict(g.degree()).values()))].append(g)
    aut=sum(1 for _ in nx.algorithms.isomorphism.GraphMatcher(g,g).isomorphisms_iter())
    mass+=factorial(v)//aut*factorial(7)
 for b in bins.values():
    for i,g in enumerate(b):
        assert not any(nx.is_isomorphic(g,h) for h in b[:i])
 expected=sum((-1)**j*comb(v,j)*perm(comb(v-j,2),7) for j in range(v+1))
 assert mass==expected
 print(v,'vertices',len(gs),'nonisomorphic graph types, labeled incidence mass',mass)
