"""Enumerate marked tree distance types and verify all mass identities exactly. Improper parents have only improper extensions."""
from itertools import permutations,product,combinations as itcombs
from functools import cache
from fractions import Fraction
import networkx as nx
from ast import literal_eval
from pathlib import Path
K=5
table={}
for line in Path(__file__).with_name("colour-sa5-r3-orbits.txt").read_text().splitlines():
 raw,num=line.rsplit(" ",1)
 k=literal_eval(raw)
 assert k not in table
 table[k]=Fraction(num)
assert min(table.values())>=0 and table[0,(),()]==1
seen=set()
def key(n,E,a):
 graph,ps=perms(n,E)
 part=min(tuple(sorted(tuple(sorted(p[i] for i in range(n) if a[i]==c)) for c in set(a))) for p in ps)
 full=n,graph,part
 seen.add(full)
 return table[full]
R=3
@cache
def perms(n,E):
 opts=[]
 for p in permutations(range(n)):
  g=tuple(sorted((*sorted((p[i],p[j])),d) for i,j,d in E))
  opts.append((g,p))
 graph=min(g for g,_ in opts)
 return graph,tuple(p for g,p in opts if g==graph)
sigs={0:{()},1:{()}}
for n in range(2,K+1):
 sigs[n]=set()
 for m in range(n,R*(n-1)+2):
  for tr in nx.nonisomorphic_trees(m):
   if max(dict(tr.degree).values())>6:continue
   leaves={i for i in tr if tr.degree[i]==1}
   if len(leaves)>n:continue
   dist=dict(nx.all_pairs_shortest_path_length(tr))
   for more in itcombs(sorted(set(tr)-leaves), n-len(leaves)):
    vs=sorted(leaves|set(more))
    E=tuple((i,j,dist[vs[i]][vs[j]]) for i,j in itcombs(range(n),2) if dist[vs[i]][vs[j]]<=R)
    sigs[n].add(perms(n,E)[0])
 for a in range(1,n):
  for e1 in sigs[a]:
   for e2 in sigs[n-a]:
    E=tuple(sorted(e1+tuple((i+a,j+a,d) for i,j,d in e2)))
    sigs[n].add(perms(n,E)[0])
 print(n,len(sigs[n]),flush=True)
checks=0
for n,E in ((n,E) for n in range(1,K+1) for E in sigs[n]):
 for v in range(n):
  others=[j for j in range(n) if j!=v]
  P=tuple(sorted((others.index(i),others.index(j),d) for i,j,d in E if v not in (i,j)))
  for a in product(range(3),repeat=n-1):
   if any(a[i]==a[j] for i,j,d in P if d==1):continue
   left=key(n-1,P,a); total=0
   for c in range(3):
    b=a[:v]+(c,)+a[v:]
    if any(b[i]==b[j] for i,j,d in E if d==1):continue
    total+=key(n,E,b)
   assert total==left
   checks+=1
assert seen==set(table)
print(len(table), "orbit weights and",checks,"exact legal-parent marginal checks")
