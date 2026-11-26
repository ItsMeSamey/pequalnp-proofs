from collections import Counter
import csv
from pathlib import Path
import sys
import networkx as nx
atlas=nx.graph_atlas_g()
counts=Counter()
exceptions=set()
with Path(sys.argv[1]).open() as f:
    for row in csv.DictReader(f,delimiter='\t'):
        if row['orders'] not in ('4,8','5,7'): continue
        small,large=row['components'].split(',')
        h=atlas[int(small[1:])]
        g=nx.from_graph6_bytes(large.encode()) if row['orders']=='4,8' else atlas[int(large[1:])]
        assert nx.is_connected(g) and nx.is_connected(h)
        assert max(dict(g.degree()).values())<=3 and g.number_of_edges()>=len(g)-1
        counts[small]+=1
        if small=='G16':
            assert min(dict(g.degree()).values())==2
            for x in g:
                test=g.copy();test.remove_node(x);assert nx.is_connected(test)
            exceptions.add(large)
        else:
            assert max(dict(h.degree()).values())==3 and h.number_of_edges()>=4
assert counts=={'G15':3,'G16':3,'G17':18,'G18':32,'G41':4,'G44':4}
assert exceptions=={'Gko`?k','GhoG_k','GMo`CK'}
print(sorted(counts.items()), '64 hosts; 24 exceptional large flag deletions connected')
