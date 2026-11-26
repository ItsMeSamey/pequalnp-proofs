import networkx as nx,itertools as it
def expand(g,v):
 h=g.copy(); n=max(h)+1
 adj=list(h[v]);h.remove_node(v)
 for i in range(3): h.add_edge(n+i,adj[i]);h.add_edge(n+i,n+(i+1)%3)
 return nx.convert_node_labels_to_integers(h)
def solve(g,removed):
 edges=[e for e in g.edges if not set(e)<=set(removed)]
 masks={v:0 for v in g if v not in removed}; vals={}; out=set()
 def rec():
  if len(vals)==len(edges):
   x=tuple(vals[next(e for e in edges if v in e and w in e)] for v in removed for w in sorted(g[v])) if removed else tuple(vals[e] for e in edges)
   conv={};out.add(tuple(conv.setdefault(a,len(conv)) for a in x));return
  candidates=[(7 & ~sumor(e),e) for e in edges if e not in vals]; m,e=min(candidates,key=lambda z:z[0].bit_count())
  used=set(vals.values())
  for c in range(3):
   if not m>>c&1 or (c not in used and any(i not in used for i in range(c))):continue
   vals[e]=c
   for v in e:
    if v in masks:masks[v]^=1<<c
   rec()
   for v in e:
    if v in masks:masks[v]^=1<<c
   del vals[e]
 def sumor(e):return masks.get(e[0],0)|masks.get(e[1],0)
 rec();return out
def run(gs):
 total=0
 for g in gs:
  es=list(g.edges);col=next(iter(solve(g,())))
  ds=[]
  for i in range(3):
   h=nx.Graph([e for e,c in zip(es,col) if c!=i]); ds.append(dict(nx.algorithms.bipartite.color(h)))
  for u,w in it.combinations(g,2):
   if g.has_edge(u,w) or any(d[u]!=d[w] for d in ds):continue
   total+=1
   table=solve(g,(u,w));bad=[a for a in sorted(table) if sorted(a[:3])==sorted(a[3:]) and len(set(a[:3]))<3]
   if total==1 or not bad:
    print(len(g),list(g.edges),u,w,len(table),len(bad),bad,sorted(table),flush=True)
 print('done',len(gs[0]),len(gs),total,flush=True)
gs=[nx.complete_graph(4)]
for n in range(4,15,2):
 run(gs)
 if n==14:break
 new=[]
 for g in gs:
  for v in g:
   h=expand(g,v)
   if not any(nx.is_isomorphic(h,z) for z in new):new.append(h)
 gs=new
