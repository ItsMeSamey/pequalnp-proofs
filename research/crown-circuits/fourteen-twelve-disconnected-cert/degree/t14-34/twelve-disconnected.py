"""Unmarked twelve-flag shapes after the independent-raw increment and historical obstructions."""
from collections import defaultdict,Counter
from itertools import combinations, combinations_with_replacement,product
from pathlib import Path
import networkx as nx
root=Path(__file__).resolve().parents[2]
src=root/'geometry/fourteen34/connected-eleven-cuts.py'
ctx={'__file__':str(src)}
exec(src.read_text().split('def add(')[0],ctx)
pool=defaultdict(list)
for g in nx.graph_atlas_g():
    if len(g)<2 or not nx.is_connected(g):continue
    md=max(dict(g.degree()).values())
    if md<=3 and ctx['ok'](g) or md==4 and len(g)==5 and g.number_of_edges()==4:
        pool[len(g)].append(g)
for n in (8,9,10):
    buckets=defaultdict(list)
    for g in pool[n-1]:
        if max(dict(g.degree()).values())>3:continue
        for k in (1,2,3):
            if g.number_of_edges()+k>13:continue
            for neighbors in combinations([i for i,d in g.degree() if d<3],k):
                h=g.copy();h.add_edges_from((n-1,w) for w in neighbors)
                if not ctx['ok'](h):continue
                key=(h.number_of_edges(),nx.weisfeiler_lehman_graph_hash(h))
                if not any(nx.is_isomorphic(h,other) for other in buckets[key]):buckets[key].append(h)
    pool[n]=[g for gs in buckets.values() for g in gs]
by=defaultdict(list)
for n,gs in pool.items():
    for g in gs:by[n,g.number_of_edges()].append(g)
def name(g):
    return g.name if g.name else nx.to_graph6_bytes(g,header=False).decode().strip()
with Path(__file__).with_suffix('.tsv').open('w') as f:
    f.write('orders\tedges\tcomponents\n'); census=Counter()
    for c in (2,3,4):
        for keys in combinations_with_replacement(sorted(by),c):
            if sum(z[0] for z in keys)!=12 or sum(z[1] for z in keys)!=14:continue
            for components in product(*(by[z] for z in keys)):
                labels=tuple(name(g) if len(g)<=7 else nx.to_graph6_bytes(g,header=False).decode().strip() for g in components)
                if any(a==b and x>y for a,b,x,y in zip(keys,keys[1:],labels,labels[1:])):continue
                ns=tuple(z[0] for z in keys);es=tuple(z[1] for z in keys)
                census[ns]+=1
                f.write(','.join(map(str,ns))+'\t'+','.join(map(str,es))+'\t'+','.join(labels)+'\n')
    print(sorted(census.items()),'total',sum(census.values()))
