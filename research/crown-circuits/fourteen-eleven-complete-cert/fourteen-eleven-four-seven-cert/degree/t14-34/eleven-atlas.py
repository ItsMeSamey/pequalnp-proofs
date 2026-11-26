"""Record the exact atlas graph IDs for small components of an eleven-flag host."""
import itertools
from collections import Counter
import networkx as nx
from pathlib import Path
root=Path(__file__).resolve().parents[2]
src=root/'geometry/fourteen34/connected-eleven-cuts.py'
ctx={'__file__':str(src)}
exec(src.read_text().split('def add(')[0],ctx)
pool=[g for g in nx.graph_atlas_g() if 2<=len(g)<=7 and nx.is_connected(g) and max(dict(g.degree()).values())<=4]
def cost(g):
 h=len(g);d=max(dict(g.degree()).values())
 return max(0,h+d-5 if d>=3 else 0,h-1 if not ctx['ok'](g) else 0)
def groups(ns):
 return (gs for gs in itertools.product(*[[g for g in pool if len(g)==n] for n in ns])
         if sum(g.number_of_edges() for g in gs)==14
         and all(len(a)!=len(b) or int(a.name[1:])<=int(b.name[1:]) for a,b in zip(gs,gs[1:])))
parts=[(4,7),(5,6),(2,2,7),(2,3,6),(2,4,5),(3,3,5),(3,4,4)]
with (Path(__file__).parent/'eleven-atlas.tsv').open('w') as f:
 f.write('orders\tgraphs\tedge_counts\tlocal_OR_floors\n')
 cache={g.name:cost(g) for g in pool}
 for ns in parts:
  counts=Counter()
  for gs in groups(ns):
   vals=tuple(g.number_of_edges() for g in gs)
   counts[vals]+=1
   fields=(ns,[g.name for g in gs],vals,[cache[g.name] for g in gs])
   f.write('\t'.join(','.join(map(str,v)) for v in fields)+'\n')
  print(ns,sum(counts.values()),dict(counts))
